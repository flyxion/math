# Lean formalization of the cubic rhombus corpus

Lean 4 and Mathlib proofs for the propositions carried by the manuscripts in `../cubic_rhombus_math`.
The object is the Gram matrix `G_d(c) = (1 - c) I + c J` of `d` unit vectors with common pairwise
inner product `c`. Dimension is written `d = n + 1`, so the manuscript factor `(1-c)^(d-1)` appears
as `(1-c)^n` with no natural number subtraction.

## Status

See `catalogue.csv`. All 14 statement classes have Lean content and none is marked partial. The
statements are listed in `REVIEW.md`, next to the manuscript claims they formalize.

| Lean theorem | Says |
|---|---|
| `det_gram` | `det G_(n+1)(c) = (1-c)^n (1 + n c)` for every real `c` |
| `facet_gram`, `principal_gram` | deleting edge vectors leaves `G_k(c)` |
| `hasDerivAt_vol2` | derivative of the volume polynomial |
| `vol2_le_one`, `vol2_eq_one_iff` | squared volume is at most 1, with equality only at `c = 0` |
| `deriv_vol2_eq_zero_iff` | `c = 0` is the only critical point |
| `vol2_two_fibres` | each value in (0,1) is taken exactly once on each side of `c = 0` |
| `quadForm_gram`, `posdef_iff` | positive definite exactly when `-1/n < c < 1` |
| `exists_system` | unit vectors in `R^(n+1)` with pairwise inner product `c` exist for `-1/n < c < 1` |
| `volume_sq_eq_det`, `volume_sq_rhombus` | Lebesgue volume of the parallelotope squares to the Gram determinant, so to `vol2 n c` |
| `volume_rhombus_le_one` | the Euclidean volume of the rhombus is at most 1 |
| `log_vol2_expansion`, `log_vol2_isBigO` | `log vol2 = -n(n+1)/2 c^2 + n(n^2-1)/3 c^3 + O(c^4)`, explicit error |
| `rank_interior`, `rank_upper`, `rank_lower` | Gram rank is `n+1` inside, `1` at `c = 1`, `n` at `c = -1/n` |
| `sysVec_isSystem`, `gram_form_unbounded` | unit vectors in `l2` with common inner product `c` exist; the Gram form is unbounded on finite sections for `c > 0` |
| `tendsto_vol2_zero`, `limit_volume_eq_one`, `limit_volume_not_injective` | limiting volume is 1 at the cube and 0 on `(0,1)` |
| `quadratic_coeff_diverges` | the quadratic coefficient of the log volume tends to `-infinity` |
| `system_linearIndependent`, `system_not_finite_dim` | infinite systems are linearly independent and fit in no finite dimensional space |
| `exists_isometry_of_ipGram_eq`, `rhombus_unique` | two families with the same Gram matrix differ by a linear isometry |
| `finrank_span_eq_rank_ipGram`, `span_dim_interior`, `span_dim_upper`, `span_dim_lower` | the span of the edge vectors has the dimension of the Gram rank |
| `cornerSet_eq_iff`, `cornerSet_two_neg` | the set of corner Gram matrices determines `c` for `d >= 3`, and does not for `d = 2` |
| `gramCol_not_mem_l2`, `no_gram_operator`, `gram_operator_zero` | for `c != 0` no operator on `l2` has the infinite Gram matrix; for `c = 0` it is the identity |
| `extremePoints_parallelepiped`, `edge_to_signed_edge` | the extreme points of a parallelotope are its vertices; an isometry carrying `P(e)` onto `P(f)` sends each edge vector to a signed edge vector |
| `congruent_rhombi_param_eq` | an isometry of `R^(m+3)` carrying a rhombus of parameter `c` onto one of parameter `s` forces `c = s` |
| `congruent_two_neg` | in dimension 2, `R_2(c)` and `R_2(-c)` are congruent |
| `tendsto_vol2` | `det G_d(a/d)` tends to `(1+a) e^(-a)` |
| `vertex_lemma` | constant pairwise sign products force `s = c` when `d >= 3` |
| `ipGram_flip2`, `parallelepiped_flip2` | in dimension 2, flipping an edge sends `c` to `-c` and the parallelogram to a translate |
| `flipGram_not_member` | for `d >= 3` the same flip leaves the family unless `c = 0` |

## What Lean does and does not certify

Lean certifies that each theorem follows from its hypotheses in Mathlib. It does not certify that a
theorem says what the corresponding manuscript says. That translation step is human work and has
not been reviewed. Remaining caveats:

1. `REVIEW.md` sets each manuscript claim beside the exact Lean statements. The faithfulness
   column is empty until a human fills it in. Lean certifies the proofs, not the translation.
2. The geometric statements are made in `EuclideanSpace R (Fin d)` with the family of `d` edge
   vectors spanning the whole space, which is the case the manuscripts treat. Rhombi whose edge
   vectors sit in a higher dimensional ambient space are covered by the Gram matrix statements.
3. The corner-set theorems (`cornerSet_eq_iff`) remain as a purely algebraic companion to the
   geometric rigidity theorem.

## Checking

```
cd lean
sh check.sh
```

This fetches the Mathlib cache, builds the library, rejects any `sorry`, and prints the axioms
each theorem depends on. All should be `propext`, `Classical.choice`, `Quot.sound`.
Toolchain: `lean-toolchain`. Mathlib revision: `lake-manifest.json`.
