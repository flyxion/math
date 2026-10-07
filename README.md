# Cubic Rhombus Research Initiative

This repository contains 14,000 mathematical manuscripts and supporting proof artifacts produced by an internal generator.

As part of generator development, we evaluate the generator on one open research object, the cubic rhombus. We expanded these evaluations after the number of manuscripts produced by our existing evaluations saturated the parameter space of a single object. Some outputs build upon earlier results produced by the generator.

This collection includes results at different stages of verification. Not all have accompanying Lean formalizations. None currently do. Some of the unformalized results could have issues. We will endeavor to fix any such issues quickly.

## Navigating the collection

The current catalogue contains 14,000 manuscripts organized into 280 families. A family groups related papers, which may include a principal result, companion arguments, consequences, or alternative proofs. Each family is classified by mathematical discipline: convex geometry.

- Start with `overview.pdf` (source `overview.tex`) for descriptions of the families and of the statement classes.
- Use `manifest.tsv` and `CONTENTS.md` to find individual papers. The `preprints/` directory has one folder per manuscript, containing the source, a citation block and build instructions.
- The shared mathematics (definitions, lemmas, one body file per contribution and dimension) is in `lib/`. Every manuscript depends on named files there.
- `ledger.jsonl` is an append-only, hash-chained event log of generation, classification and review. `make ledger` verifies it.
- `classes.json` lists the distinct statements and the manuscripts that carry each.

## What the numbers mean

- Parameter points of the generator: 967,680.
- Manuscripts in this release: 14,000.
- Nominal families (dimension, geometry, topology): 280.
- Distinct statements among all 967,680 points, computed by comparing exact content: 14.
- Distinct statements present in this release: 14.
- Manuscripts per distinct statement in this release: 1,000.0 on average.

Seven parameters appear in each title. Two of them, the dimension and the contribution, select the proposition proved. The other five are carried as metadata and are not used by any proof. Counting manuscripts is therefore not counting results. This repository does not support the hypothesis that its manuscripts are independent mathematical contributions.

## Reasoning summaries

We are also releasing abridged summaries of the reasoning for every statement class, with worked instances computed in SymPy.

| Class | Scope | Manuscripts in release | Parameter points | Subject |
|---|---|---|---|---|
| [S01](reasoning_traces/S01.md) | general n | 1,490 | 103,680 | T1: existence, uniqueness up to orthogonal maps, and the positivity range of the Gram matrix |
| [S02](reasoning_traces/S02.md) | general n | 3,030 | 207,360 | T2: volume is at most 1, with equality only for the unit cube; T3: the cube is the unique maximizer and unique critical point of the volume |
| [S03](reasoning_traces/S03.md) | general n | 1,465 | 103,680 | T4: second and third order expansion of the log volume at the cube |
| [S04](reasoning_traces/S04.md) | general n | 1,513 | 103,680 | T5: rank of the edge system at interior and endpoint values of the parameter |
| [S05](reasoning_traces/S05.md) | general n | 1,510 | 103,680 | T6: facets are lower dimensional members of the family, and the boundary determines the parameter exactly when n is at least 3 |
| [S06](reasoning_traces/S06.md) | general n | 1,744 | 120,960 | T7: exact value of det G_n(a/n) and its limit (1+a)exp(-a) |
| [S07](reasoning_traces/S07.md) | general n | 1,224 | 86,400 | T8: volume takes each value in (0,1) exactly twice, with shape consequences that depend on n |
| [S08](reasoning_traces/S08.md) | n = 2 only | 259 | 17,280 | T8: volume takes each value in (0,1) exactly twice, with shape consequences that depend on n (in dimension 2 the partner of c is -c, and R_2(c), R_2(-c) are congruent) |
| [S09](reasoning_traces/S09.md) | infinite dimension | 254 | 17,280 | T1: unit vector systems with equal inner products exist for 0 <= c <= 1, and the Gram operator is bounded on l2 only for c = 0 |
| [S10](reasoning_traces/S10.md) | infinite dimension | 514 | 34,560 | T2: limiting volume is 1 at c = 0 and 0 for 0 < c < 1; T3: the cube is the unique maximizer of the limiting volume |
| [S11](reasoning_traces/S11.md) | infinite dimension | 256 | 17,280 | T4: the quadratic coefficient of the log volume diverges with the dimension |
| [S12](reasoning_traces/S12.md) | infinite dimension | 260 | 17,280 | T5: for 0 <= c < 1 the system is linearly independent and fits in no finite dimensional space |
| [S13](reasoning_traces/S13.md) | infinite dimension | 228 | 17,280 | T6: for every finite section of order at least 3 the boundary determines c |
| [S14](reasoning_traces/S14.md) | infinite dimension | 253 | 17,280 | T8: the limiting volume is constant on (0,1), so volume does not determine c |

## How the results were produced

The vast majority of results were obtained with the same procedure: a seeded sample of the Cartesian product of seven parameter lists, followed by classification of each sampled point by the exact content of the proposition it carries. Each result used a small fraction of a CPU second. The generator was posed 14,000 problems. Requiring an appropriate level of significance is a command line option that is accepted and not consulted.

Exceptions to this fixed procedure: none. No part of the corpus was human edited for readability.

## Verification

- Exact SymPy checks: 19 of 19 passed. They confirm closed forms against explicit matrices for n = 2 through 8, and the symbolic identities in n.
- Human review: none.
- Independent scrutiny: none.
- Lean: not attempted. A Lean formalization of the lemma on the spectrum of (1-c)I + cJ would be the natural first target.
- Novelty: not assessed.

## Versions and citations

We will preserve the public release history of this collection. Corrections and revisions will be recorded as new versions, with previously released versions remaining accessible. To cite an individual manuscript, use the BibTeX block in its directory.

Ledger head for release 1.0: `e4360a569bc0b07ff7eec957c147fbe5d3558a3126094594769898e19849e667`

## Reproducing

```
python3 tools/industrial_mathematics.py generate --target 14000 --seed 1 --out <dir>
```

The output is deterministic for a given seed and target.
