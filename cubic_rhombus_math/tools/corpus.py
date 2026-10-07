"""
corpus.py

Parameter space, sampling, naming, classification, the hash-chained ledger,
and the repository-level documents (README, CONTENTS, overview, traces).
"""

import hashlib
import json
import os
import random
import re
import shutil
import subprocess
import time
from collections import defaultdict

import sympy as sp

import render
import verify
from rhombus import (CONTRIBUTIONS, DIM_LABELS, LABELS, a, build_classes, c,
                     canon_content, gram, n, spec_content)

VERSION = "1.0"

GEOMETRIES = ["Euclidean", "hyperbolic", "spherical", "Minkowskian",
              "Finsler", "sub-Riemannian", "ultrametric", "weighted"]
TOPOLOGIES = ["simply connected", "toroidal", "non-orientable", "stratified", "fractal"]
REGULARITIES = ["smooth", "Lipschitz", "weak Sobolev", "Holder-continuous", "BV", "measurable"]
BOUNDARIES = ["Dirichlet", "Neumann", "periodic", "Robin", "free", "mixed", "absorbing", "reflecting"]
PROOFS = ["variational", "spectral", "probabilistic", "category-theoretic", "combinatorial",
          "ergodic", "computer-assisted", "homotopical", "an alternative"]

AXES = [DIM_LABELS, GEOMETRIES, TOPOLOGIES, REGULARITIES, BOUNDARIES, PROOFS, CONTRIBUTIONS]
TOTAL = 1
for ax in AXES:
    TOTAL *= len(ax)

MONTHS = ["September", "October"]


def decode(index):
    """Mixed-radix decode of an index in [0, TOTAL) into one value per axis."""
    vals = []
    for ax in reversed(AXES):
        index, r = divmod(index, len(ax))
        vals.append(ax[r])
    return tuple(reversed(vals))


def make_params(vals):
    dim, g, top, reg, bd, proof, t = vals
    return {"dim": dim, "g": g, "top": top, "reg": reg, "bd": bd, "proof": proof, "t": t}


def make_title(p):
    dimphrase = "Infinite Dimension" if p["dim"] == "infinite" else f"Dimension {p['dim']}"
    g = p["g"][0].upper() + p["g"][1:]
    proof = "An Alternative Proof" if p["proof"] == "an alternative" else p["proof"].capitalize() + " Proof"
    return (f"{LABELS[p['t']]} for the {g} Cubic Rhombus in {dimphrase} "
            f"({p['top']}, {p['reg']}, {p['bd']} boundary conditions): {proof}")


def slug(title):
    s = re.sub(r"[^A-Za-z0-9]+", "-", title).strip("-")
    return s



def sha256_text(s):
    return hashlib.sha256(s.encode("utf-8")).hexdigest()


class Ledger:
    """Append-only, hash-chained event log.  Each record's hash covers the
    previous hash and the record body, so editing any past event breaks every
    later hash."""

    def __init__(self, path):
        self.path = path
        self.f = open(path, "w", encoding="utf-8")
        self.prev = "0" * 64
        self.seq = 0

    def add(self, event, **data):
        rec = {"seq": self.seq, "prev": self.prev, "event": event, "data": data}
        body = json.dumps(rec, sort_keys=True, separators=(",", ":"))
        rec["hash"] = sha256_text(self.prev + body)
        self.f.write(json.dumps(rec, sort_keys=True, separators=(",", ":")) + "\n")
        self.prev = rec["hash"]
        self.seq += 1

    def close(self):
        self.f.close()
        return self.prev


def check_ledger(out):
    path = os.path.join(out, "ledger.jsonl")
    prev, count, bad_files = "0" * 64, 0, []
    with open(path, encoding="utf-8") as f:
        for line in f:
            rec = json.loads(line)
            h = rec.pop("hash")
            if rec["prev"] != prev:
                return False, f"chain broken at seq {rec['seq']}"
            body = json.dumps(rec, sort_keys=True, separators=(",", ":"))
            if sha256_text(prev + body) != h:
                return False, f"hash mismatch at seq {rec['seq']}"
            prev = h
            count += 1
            if rec["event"] == "GENERATED":
                d = rec["data"]
                p = os.path.join(out, "preprints", d["dir"], "manuscript.tex")
                if os.path.exists(p):
                    with open(p, encoding="utf-8") as g:
                        if sha256_text(g.read()) != d["tex_sha256"]:
                            bad_files.append(d["id"])
    if bad_files:
        return False, f"{len(bad_files)} manuscript files differ from their ledger hash, first {bad_files[0]}"
    return True, f"{count} events, head {prev}"


def compile_pdf(directory, tex, runs=2):
    ok = True
    for _ in range(runs):
        r = subprocess.run(["pdflatex", "-interaction=nonstopmode", "-halt-on-error", tex],
                           cwd=directory, capture_output=True, text=True)
        if r.returncode != 0:
            ok = False
            break
    stem = tex[:-4]
    for ext in ("aux", "log", "out"):
        try:
            os.remove(os.path.join(directory, f"{stem}.{ext}"))
        except FileNotFoundError:
            pass
    return ok


# ---------------------------------------------------------------------------
# Worked instances for reasoning traces
# ---------------------------------------------------------------------------

def worked(t, k):
    G = gram(k)
    det = sp.factor(G.det())
    out = [f"Gram matrix G_{k}(c) = {G.tolist()}"]
    out.append(f"det G_{k}(c) = {det}")
    if t == "T1":
        out.append(f"eigenvalues with multiplicity: {G.eigenvals()}")
    if t in ("T2", "T3"):
        out.append(f"d/dc det = {sp.factor(sp.diff(det, c))}")
        out.append("critical points: " + str(sp.solve(sp.diff(det, c), c)) + ", only c = 0 lies in the open interval")
        out.append(f"det at c = 0: {det.subs(c, 0)}")
    if t == "T4":
        ser = sp.series(sp.log(sp.expand(G.det())), c, 0, 4)
        out.append(f"series of ln det: {ser}")
    if t == "T5":
        lo = -sp.Rational(1, k - 1)
        out.append(f"rank at c = 0: {G.subs(c, 0).rank()}, at c = {lo}: {G.subs(c, lo).rank()}, at c = 1: {G.subs(c, 1).rank()}")
    if t == "T6":
        out.append(f"principal submatrix of order {k - 1}: {G[:k - 1, :k - 1].tolist()}")
        out.append(f"depends on c: {c in G[:k - 1, :k - 1].free_symbols}")
    if t == "T7":
        out.append(f"det G_{k}(a/{k}) = {sp.simplify(det.subs(c, a / k))}")
    if t == "T8":
        lo = -sp.Rational(1, k - 1)
        P = sp.Poly(sp.expand(det - sp.Rational(1, 4)), c)
        roots = [r for r in P.nroots() if lo < sp.re(r) < 1 and abs(sp.im(r)) < 1e-12]
        out.append(f"real roots of det = 1/4 in ({lo}, 1): {[round(float(sp.re(r)), 6) for r in roots]}")
    return out


def trace_md(rec):
    lines = [f"# Reasoning summary, class {rec['id']}", ""]
    lines.append(f"Scope: {rec['scope']}.")
    lines.append("")
    lines.append("Statement content: `" + canon_content(rec["content"]) + "`")
    lines.append("")
    lines.append("Summary: " + render.class_summary(rec))
    lines.append("")
    lines.append("Members (contribution, dimension): " + ", ".join(f"{t}/{d}" for t, d in rec["members"]))
    lines.append("")
    t0 = rec["members"][0][0]
    if rec["scope"] == "infinite dimension":
        lines.append("Derivation: see lib/body for the infinite-dimension proof. The finite sections are governed by Lemma 1 (spectrum), "
                     "which gives det G_n(c) = (1-c)^(n-1) (1 + (n-1)c); the infinite statements are limits or constructions built on it.")
    else:
        k = 2 if rec["scope"] == "n = 2 only" else 3
        lines.append(f"Worked instance, n = {k}:")
        lines.append("")
        for s in worked(t0, k):
            lines.append(f"- {s}")
    lines.append("")
    lines.append("Every step above is one line of computation from the matrix (1-c) I + c J. "
                 "The reasoning behind this class took no more effort than the reasoning behind any other class.")
    lines.append("")
    lines.append("This summary does not support the hypothesis that this class is an independent mathematical contribution.")
    return "\n".join(lines) + "\n"


# ---------------------------------------------------------------------------
# Main generation driver
# ---------------------------------------------------------------------------

def generate(a_):
    t_start = time.time()
    render.AUTHOR = a_.author
    out = os.path.abspath(a_.out)
    n_target = min(a_.target, TOTAL)
    rng = random.Random(a_.seed)

    print(f"Parameter space for one cubic rhombus: {TOTAL:,} potential manuscripts")
    print("Generating candidate mathematical literature...")
    indices = sorted(rng.sample(range(TOTAL), n_target))
    params = [make_params(decode(i)) for i in indices]

    print("Running exact verification (SymPy)...")
    if a_.skip_verify:
        vres = []
        print("  verification skipped by request")
    else:
        vres = verify.run_all()
        vs = verify.summary(vres)
        print(f"  {vs['passed']}/{vs['checks']} exact checks passed")
        if vs["failed"]:
            raise SystemExit("verification failed: " + "; ".join(vs["failed"]))

    print("Classifying statements by content...")
    classes, index = build_classes()
    by_id = {r["id"]: r for r in classes}

    print("Aggregating manuscripts into result families...")
    fam_keys = sorted({(DIM_LABELS.index(p["dim"]), GEOMETRIES.index(p["g"]), TOPOLOGIES.index(p["top"])) for p in params})
    fam_no = {k: i + 1 for i, k in enumerate(fam_keys)}
    counters = defaultdict(int)
    manuscripts = []
    for p in params:
        fk = (DIM_LABELS.index(p["dim"]), GEOMETRIES.index(p["g"]), TOPOLOGIES.index(p["top"]))
        counters[fk] += 1
        mid = f"CR-{fam_no[fk]:03d}-{counters[fk]:03d}"
        title = make_title(p)
        m = dict(p)
        m.update({"id": mid, "family": fam_no[fk], "title": title,
                  "title_tex": title.replace("&", r"\&"),
                  "dir": slug(title),
                  "class": index[(p["t"], p["dim"])]})
        manuscripts.append(m)

    cls_count = defaultdict(int)
    principal = {}
    for m in manuscripts:
        cls_count[m["class"]] += 1
        principal.setdefault(m["class"], m["id"])

    print("Assigning significance classifications "
          f"(threshold {a_.significance_threshold}, unused)...")
    print(f"Human review: {'enabled (ignored)' if a_.human_review else 'disabled'}")
    print("Formal verification (Lean): not attempted")
    print("Potential issues: acknowledged")

    # class sizes over the full parameter space (computed, then cross-checked)
    per_pair = TOTAL // (len(DIM_LABELS) * len(CONTRIBUTIONS))
    full_size = {r["id"]: per_pair * len(r["members"]) for r in classes}
    assert sum(full_size.values()) == TOTAL, "class sizes do not partition the parameter space"

    os.makedirs(out, exist_ok=True)
    pre = os.path.join(out, "preprints")
    os.makedirs(pre, exist_ok=True)
    lib_files = render.write_lib(os.path.join(out, "lib"))

    # per-class verification status
    class_check = {}
    for r in classes:
        nchk, allok = verify.class_status(vres, r["members"]) if vres else (0, False)
        class_check[r["id"]] = (nchk, allok)

    led = Ledger(os.path.join(out, "ledger.jsonl"))
    led.add("RELEASE", version=VERSION, author=a_.author, seed=a_.seed, target=n_target, parameter_space=TOTAL,
            generator="industrial_mathematics.py")
    for r in classes:
        nchk, allok = class_check[r["id"]]
        led.add("CLASS", id=r["id"], scope=r["scope"], content=canon_content(r["content"]),
                members=[f"{t}/{d}" for t, d in r["members"]], checks=nchk, checks_passed=bool(allok))
    for chk in vres:
        led.add("CAS_CHECK", name=chk["name"], tags=chk["tags"], ok=chk["ok"])

    emit = a_.emit
    manifest = []
    emitted = 0
    for m in manuscripts:
        cls = by_id[m["class"]]
        info = {"count": cls_count[m["class"]], "principal": principal[m["class"]],
                "checks": class_check[m["class"]][0]}
        tex = render.manuscript_tex(m, cls, info)
        h = sha256_text(tex)
        write = emit == "all" or (emit == "principal" and principal[m["class"]] == m["id"])
        if write:
            d = os.path.join(pre, m["dir"])
            os.makedirs(d, exist_ok=True)
            with open(os.path.join(d, "manuscript.tex"), "w", encoding="utf-8") as f:
                f.write(tex)
            with open(os.path.join(d, "citation.bib"), "w", encoding="utf-8") as f:
                f.write(citation(m))
            with open(os.path.join(d, "BUILD.md"), "w", encoding="utf-8") as f:
                f.write(build_md(m))
            emitted += 1
        led.add("GENERATED", id=m["id"], dir=m["dir"], tex_sha256=h, written=write,
                params={k: m[k] for k in ("dim", "g", "top", "reg", "bd", "proof", "t")})
        led.add("CLASSIFIED", id=m["id"], cls=m["class"])
        led.add("REVIEW", id=m["id"], human_review="none", lean="not attempted",
                independent_scrutiny="none")
        manifest.append(f"{m['id']}\t{m['dir']}\t{m['class']}\t{m['title']}")
    head = led.close()

    with open(os.path.join(out, "manifest.tsv"), "w", encoding="utf-8") as f:
        f.write("id\tdirectory\tclass\ttitle\n" + "\n".join(manifest) + "\n")
    with open(os.path.join(out, "classes.json"), "w", encoding="utf-8") as f:
        json.dump([{"id": r["id"], "scope": r["scope"], "content": canon_content(r["content"]),
                    "members": [f"{t}/{d}" for t, d in r["members"]],
                    "points_in_parameter_space": full_size[r["id"]],
                    "manuscripts_in_release": cls_count.get(r["id"], 0)} for r in classes],
                  f, indent=2)

    # traces
    os.makedirs(os.path.join(out, "reasoning_traces"), exist_ok=True)
    for r in classes:
        with open(os.path.join(out, "reasoning_traces", f"{r['id']}.md"), "w", encoding="utf-8") as f:
            f.write(trace_md(r))

    stats = {
        "n": len(manuscripts), "families": len(fam_keys), "classes_in_release": len(cls_count),
        "classes_total": len(classes), "emitted": emitted, "head": head,
        "checks": len(vres), "passed": sum(x["ok"] for x in vres),
    }
    with open(os.path.join(out, "README.md"), "w", encoding="utf-8") as f:
        f.write(readme(stats, classes, cls_count, full_size, a_))
    with open(os.path.join(out, "CONTENTS.md"), "w", encoding="utf-8") as f:
        f.write(contents_md(manuscripts, fam_keys, fam_no))
    with open(os.path.join(out, "overview.tex"), "w", encoding="utf-8") as f:
        f.write(overview_tex(stats, classes, cls_count, full_size))
    with open(os.path.join(out, "Makefile"), "w", encoding="utf-8") as f:
        f.write(MAKEFILE)
    with open(os.path.join(out, "LICENSE"), "w", encoding="utf-8") as f:
        f.write("Public domain. CC0 1.0 Universal dedication.\n")
    tools = os.path.join(out, "tools")
    os.makedirs(tools, exist_ok=True)
    here = os.path.dirname(os.path.abspath(__file__))
    for fn in ("rhombus.py", "verify.py", "corpus.py", "render.py", "industrial_mathematics.py"):
        shutil.copy(os.path.join(here, fn), os.path.join(tools, fn))

    pdfs = []
    if not a_.no_pdf:
        print("Compiling overview and sample manuscripts...")
        if compile_pdf(out, "overview.tex"):
            pdfs.append("overview.pdf")
        samples = [principal[r["id"]] for r in classes if r["id"] in principal][: a_.pdf_samples]
        for m in manuscripts:
            if m["id"] in samples and emit != "none":
                d = os.path.join(pre, m["dir"])
                if os.path.exists(os.path.join(d, "manuscript.tex")) and compile_pdf(d, "manuscript.tex"):
                    pdfs.append(os.path.join("preprints", m["dir"], "manuscript.pdf"))
        print(f"  compiled {len(pdfs)} PDF files")

    print()
    print(f"Research productivity: {stats['n']:,} manuscripts in {stats['families']:,} families")
    print(f"Distinct statements among them: {stats['classes_in_release']} "
          f"(parameter space: {TOTAL:,} points, {len(classes)} distinct statements, "
          f"ratio {TOTAL // len(classes):,} to 1)")
    print(f"Ledger head: {head}")
    print(f"Wrote {out} ({emitted:,} manuscript folders, {len(lib_files)} library files) "
          f"in {time.time() - t_start:.1f} s")
    return stats, pdfs


def tex_escape(text):
    out = []
    for ch in text:
        out.append({"\\": r"\textbackslash{}", "&": r"\&", "%": r"\%", "$": r"\$", "#": r"\#",
                    "_": r"\_", "{": r"\{", "}": r"\}", "~": r"\textasciitilde{}",
                    "^": r"\textasciicircum{}"}.get(ch, ch))
    return "".join(out)


def citation(m):
    return (f"@misc{{{m['id']},\n"
            f"  author = {{{render.AUTHOR}}},\n"
            f"  title = {{{m['title']}}},\n"
            f"  year = {{2026}},\n"
            f"  howpublished = {{Cubic Rhombus Research Initiative, manuscript {m['id']}, class {m['class']}}},\n"
            f"  note = {{Release {VERSION}. Does not support the hypothesis that it is an independent mathematical contribution.}}\n"
            f"}}\n")


def build_md(m):
    lemmas = "lemmas_inf" if m["dim"] == "infinite" else "lemmas"
    return (f"# Building manuscript {m['id']}\n\n"
            "Run `pdflatex manuscript.tex` twice in this directory.\n\n"
            "Library files used, relative to this directory:\n\n"
            "- `../../lib/preamble.tex`\n"
            f"- `../../lib/{lemmas}.tex`\n"
            f"- `../../lib/body/{m['t']}_{m['dim']}.tex`\n"
            "- `../../lib/refs.tex`\n\n"
            f"Statement class: {m['class']}. Human review: none. Lean: not attempted.\n")


MAKEFILE = """# make pdf DIR=preprints/<directory>   builds one manuscript
# make overview                        builds overview.pdf
# make ledger                          verifies the hash chain
pdf:
\tcd $(DIR) && pdflatex -interaction=nonstopmode manuscript.tex && pdflatex -interaction=nonstopmode manuscript.tex

overview:
\tpdflatex -interaction=nonstopmode overview.tex && pdflatex -interaction=nonstopmode overview.tex

ledger:
\tpython3 tools/industrial_mathematics.py ledger-check --out .

verify:
\tcd tools && python3 verify.py
"""


def readme(stats, classes, cls_count, full_size, a_):
    K = len(classes)
    lines = []
    A = lines.append
    A("# Cubic Rhombus Research Initiative")
    A("")
    A(f"This repository contains {stats['n']:,} mathematical manuscripts and supporting proof artifacts produced by an internal generator.")
    A("")
    A("As part of generator development, we evaluate the generator on one open research object, the cubic rhombus. "
      "We expanded these evaluations after the number of manuscripts produced by our existing evaluations saturated the parameter space of a single object. "
      "Some outputs build upon earlier results produced by the generator.")
    A("")
    A("This collection includes results at different stages of verification. Not all have accompanying Lean formalizations. "
      "None currently do. Some of the unformalized results could have issues. We will endeavor to fix any such issues quickly.")
    A("")
    A("## Navigating the collection")
    A("")
    A(f"The current catalogue contains {stats['n']:,} manuscripts organized into {stats['families']:,} families. "
      "A family groups related papers, which may include a principal result, companion arguments, consequences, or alternative proofs. "
      "Each family is classified by mathematical discipline: convex geometry.")
    A("")
    A("- Start with `overview.pdf` (source `overview.tex`) for descriptions of the families and of the statement classes.")
    A("- Use `manifest.tsv` and `CONTENTS.md` to find individual papers. The `preprints/` directory has one folder per manuscript, containing the source, a citation block and build instructions.")
    A("- The shared mathematics (definitions, lemmas, one body file per contribution and dimension) is in `lib/`. Every manuscript depends on named files there.")
    A("- `ledger.jsonl` is an append-only, hash-chained event log of generation, classification and review. `make ledger` verifies it.")
    A("- `classes.json` lists the distinct statements and the manuscripts that carry each.")
    A("")
    A("## What the numbers mean")
    A("")
    A(f"- Parameter points of the generator: {TOTAL:,}.")
    A(f"- Manuscripts in this release: {stats['n']:,}.")
    A(f"- Nominal families (dimension, geometry, topology): {stats['families']:,}.")
    A(f"- Distinct statements among all {TOTAL:,} points, computed by comparing exact content: {K}.")
    A(f"- Distinct statements present in this release: {stats['classes_in_release']}.")
    A(f"- Manuscripts per distinct statement in this release: {stats['n'] / max(stats['classes_in_release'], 1):,.1f} on average.")
    A("")
    A("Seven parameters appear in each title. Two of them, the dimension and the contribution, select the proposition proved. "
      "The other five are carried as metadata and are not used by any proof. "
      "Counting manuscripts is therefore not counting results. "
      "This repository does not support the hypothesis that its manuscripts are independent mathematical contributions.")
    A("")
    A("## Reasoning summaries")
    A("")
    A("We are also releasing abridged summaries of the reasoning for every statement class, with worked instances computed in SymPy.")
    A("")
    A("| Class | Scope | Manuscripts in release | Parameter points | Subject |")
    A("|---|---|---|---|---|")
    for r in classes:
        A(f"| [{r['id']}](reasoning_traces/{r['id']}.md) | {r['scope']} | {cls_count.get(r['id'], 0):,} | {full_size[r['id']]:,} | {render.class_summary(r)} |")
    A("")
    A("## How the results were produced")
    A("")
    A("The vast majority of results were obtained with the same procedure: a seeded sample of the Cartesian product of seven parameter lists, "
      "followed by classification of each sampled point by the exact content of the proposition it carries. "
      f"Each result used a small fraction of a CPU second. The generator was posed {stats['n']:,} problems. "
      "Requiring an appropriate level of significance is a command line option that is accepted and not consulted.")
    A("")
    A("Exceptions to this fixed procedure: none. No part of the corpus was human edited for readability.")
    A("")
    A("## Verification")
    A("")
    A(f"- Exact SymPy checks: {stats['passed']} of {stats['checks']} passed. They confirm closed forms against explicit matrices for n = 2 through 8, and the symbolic identities in n.")
    A("- Human review: none.")
    A("- Independent scrutiny: none.")
    A("- Lean: not attempted. A Lean formalization of the lemma on the spectrum of (1-c)I + cJ would be the natural first target.")
    A("- Novelty: not assessed.")
    A("")
    A("## Versions and citations")
    A("")
    A("We will preserve the public release history of this collection. Corrections and revisions will be recorded as new versions, with previously released versions remaining accessible. "
      "To cite an individual manuscript, use the BibTeX block in its directory.")
    A("")
    A(f"Ledger head for release {VERSION}: `{stats['head']}`")
    A("")
    A("## Reproducing")
    A("")
    A("```")
    A(f"python3 tools/industrial_mathematics.py generate --target {a_.target} --seed {a_.seed} --author {a_.author} --out <dir>")
    A("```")
    A("")
    A("The output is deterministic for a given seed and target.")
    return "\n".join(lines) + "\n"


def contents_md(manuscripts, fam_keys, fam_no):
    by_fam = defaultdict(list)
    for m in manuscripts:
        by_fam[m["family"]].append(m)
    lines = ["# Contents", "",
             "Family classification: convex geometry. Lean: not attempted for any entry. Reviewed: no for every entry.", ""]
    inv = {v: k for k, v in fam_no.items()}
    for fam in sorted(by_fam):
        di, gi, ti = inv[fam]
        dim = DIM_LABELS[di]
        lines.append(f"## Family {fam:03d}: dimension {dim}, {GEOMETRIES[gi]}, {TOPOLOGIES[ti]} ({len(by_fam[fam])} manuscripts)")
        lines.append("")
        for m in by_fam[fam]:
            lines.append(f"- {m['id']} [{m['class']}] [{m['title']}](preprints/{m['dir']}/manuscript.tex)")
        lines.append("")
    return "\n".join(lines) + "\n"


def overview_tex(stats, classes, cls_count, full_size):
    rows = []
    for r in classes:
        members = ", ".join(f"{t}/{d}" for t, d in r["members"])
        rows.append(f"{r['id']} & {r['scope']} & {cls_count.get(r['id'], 0):,} & {full_size[r['id']]:,} \\\\")
    desc = []
    for r in classes:
        txt = tex_escape(render.class_summary(r))
        desc.append(f"\\item[{r['id']}] {txt}.")
    K = len(classes)
    return rf"""\documentclass[11pt]{{article}}
\input{{lib/preamble}}
\title{{Overview of the Cubic Rhombus Research Initiative}}
\author{{{render.AUTHOR}}}
\date{{Release {VERSION}}}
\begin{{document}}
\maketitle
\section{{What the release contains}}
The release contains {stats['n']:,} manuscripts in {stats['families']:,} nominal families. Each manuscript is a proposition about one object, the cubic rhombus $R_n(c)$ with Gram matrix $(1-c)I+cJ$, under a title that carries seven parameters. The parameter space has {TOTAL:,} points: 7 dimensions, 8 geometries, 5 topologies, 6 regularities, 8 boundary conditions, 9 proof techniques and 8 contributions.

\section{{Which parameters are used}}
Two parameters, the dimension and the contribution, select the proposition proved. The other five are carried in the title and are not used by any proof. A point of the parameter space is therefore determined, as far as mathematical content is concerned, by one of $7\times8=56$ pairs. Each pair has $17{{,}}280$ preimages.

\section{{Statement classes}}
For each of the 56 pairs the generator computes the exact content of the proposition: closed forms, domains, ranks, coefficients and fibre counts, computed from explicit matrices for $n\le6$ and from closed forms for general $n$. Two pairs are placed in one class when their contents coincide, or when the content for a specific dimension is obtained from the general $n$ content by substitution. The result is {K} classes.

\begin{{center}}
\small
\begin{{tabular}}{{llrr}}
\toprule
Class & Scope & In release & Parameter points \\
\midrule
{chr(10).join(rows)}
\bottomrule
\end{{tabular}}
\end{{center}}

\begin{{description}}
{chr(10).join(desc)}
\end{{description}}

\section{{Redundancy}}
The {TOTAL:,} parameter points carry {K} distinct statements, a ratio of {TOTAL // K:,} to $1$. The {stats['n']:,} manuscripts of this release carry {stats['classes_in_release']} of them. These ratios are computed, not estimated.

\section{{What this overview does not show}}
It does not show that any of the {K} statements is new, interesting, or significant. It does not show that the classification is the only reasonable one. It does not support the hypothesis that the manuscripts of this release are independent mathematical contributions.
\end{{document}}
"""
