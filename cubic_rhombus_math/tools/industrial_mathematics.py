#!/usr/bin/env python3
"""
industrial_mathematics.py

Generates a mathematical research corpus from a single seed object, the cubic
rhombus R_n(c) with Gram matrix (1-c)I + cJ, by sampling the Cartesian product
of seven parameter lists.  Every manuscript carries a true proposition with a
proof, the propositions are classified by exact content, and the classification
shows how few distinct statements the manuscripts carry.

Subcommands:
    generate      build a corpus (default when no subcommand is given)
    verify        run the exact SymPy checks only
    classes       print the statement classes and their sizes
    ledger-check  verify the hash chain and manuscript hashes of a corpus

Nothing here establishes that any manuscript is an independent result.
That is the point. The code is the argument.
"""

import argparse
import sys


def build_parser():
    ap = argparse.ArgumentParser(description="Industrial mathematical productivity engine.")
    sub = ap.add_subparsers(dest="cmd")

    g = sub.add_parser("generate", help="build a corpus")
    g.add_argument("--target", type=int, default=14000, help="stop at this level of institutional productivity")
    g.add_argument("--seed", type=int, default=1)
    g.add_argument("--author", default="Anonymous", help="author name for manuscripts, citations and overview")
    g.add_argument("--out", default="cubic_rhombus_math")
    g.add_argument("--significance-threshold", type=float, default=1.0, help="accepted, logged, and ignored")
    g.add_argument("--human-review", action="store_true", default=False, help="accepted, logged, and ignored")
    g.add_argument("--emit", choices=["none", "principal", "all"], default="all",
                   help="which manuscript folders to write (principal = first member of each class)")
    g.add_argument("--no-pdf", action="store_true", help="do not compile PDFs")
    g.add_argument("--pdf-samples", type=int, default=3, help="number of principal manuscripts to compile")
    g.add_argument("--skip-verify", action="store_true", help="skip the exact checks (not recommended)")

    sub.add_parser("verify", help="run the exact checks only")
    sub.add_parser("classes", help="print statement classes")

    lc = sub.add_parser("ledger-check", help="verify a corpus ledger")
    lc.add_argument("--out", default="cubic_rhombus_math")
    return ap


def main(argv=None):
    argv = list(sys.argv[1:] if argv is None else argv)
    if not argv or argv[0].startswith("-") and argv[0] not in ("-h", "--help"):
        argv = ["generate"] + argv
    args = build_parser().parse_args(argv)

    if args.cmd == "verify":
        import verify
        res = verify.run_all()
        for r in res:
            print(("PASS " if r["ok"] else "FAIL ") + r["name"])
        s = verify.summary(res)
        print(f"\n{s['passed']}/{s['checks']} checks passed")
        return 0 if not s["failed"] else 1

    if args.cmd == "classes":
        import corpus
        import render
        from rhombus import build_classes, canon_content
        classes, _ = build_classes()
        per_pair = corpus.TOTAL // (7 * 8)
        for r in classes:
            print(f"{r['id']}  {r['scope']:<20} {per_pair * len(r['members']):>8,} points  "
                  f"{render.class_summary(r)}")
        print(f"\n{corpus.TOTAL:,} parameter points, {len(classes)} distinct statements")
        return 0

    if args.cmd == "ledger-check":
        import corpus
        ok, msg = corpus.check_ledger(args.out)
        print(("OK: " if ok else "FAILED: ") + msg)
        return 0 if ok else 1

    import corpus
    corpus.generate(args)
    return 0


if __name__ == "__main__":
    sys.exit(main())
