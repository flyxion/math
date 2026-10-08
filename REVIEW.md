# Statement review sheet

For each class, the manuscript claim (from `industrial_mathematics.py classes`) is set beside the exact Lean statements that formalize it. Lean certifies that the Lean statements are proved. Whether they say what the manuscript says is a human judgment, and this sheet is where that judgment is made. Put a name and a date next to each class when you have read it.

Dimension convention: manuscript dimension `d` is `n + 1` in Lean, and the squared volume is `vol2 n c = (1-c)^n (1+n c)`.


## S01  (T1 (general n), done)

**Manuscript claim** (general n): T1: existence, uniqueness up to orthogonal maps, and the positivity range of the Gram matrix

**Notes:** Determinant, exact positivity range, existence of unit vectors in R^(n+1) with the stated Gram matrix, and uniqueness: any two families with the same Gram matrix differ by a linear isometry of R^(n+1).

```lean
theorem det_gram (n : ℕ) (c : ℝ) : (gram (n + 1) c).det = vol2 n c
```

```lean
theorem posdef_iff {n : ℕ} (hn : 1 ≤ n) {c : ℝ} :
    (∀ x : Fin (n + 1) → ℝ, x ≠ 0 → 0 < x ⬝ᵥ (gram (n + 1) c).mulVec x) ↔
      (-1 < n * c ∧ c < 1)
```

```lean
theorem quadForm_gram {d : ℕ} (c : ℝ) (x : Fin d → ℝ) :
    x ⬝ᵥ (gram d c).mulVec x = (1 - c) * ∑ i, x i ^ 2 + c * (∑ i, x i) ^ 2
```

```lean
theorem posSemidef_gram {n : ℕ} {c : ℝ} (hlo : -1 < n * c) (hhi : c < 1) :
    (gram (n + 1) c).PosSemidef
```

```lean
theorem exists_system {n : ℕ} {c : ℝ} (hlo : -1 < n * c) (hhi : c < 1) :
    ∃ e : Fin (n + 1) → EuclideanSpace ℝ (Fin (n + 1)), ipGram e = gram (n + 1) c
```

```lean
theorem exists_isometry_of_ipGram_eq (e f : Fin d → EuclideanSpace ℝ (Fin d))
    (h : ipGram e = ipGram f) :
    ∃ T : EuclideanSpace ℝ (Fin d) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin d), ∀ i, T (e i) = f i
```

```lean
theorem rhombus_unique {n : ℕ} {c : ℝ} (e f : Fin (n + 1) → EuclideanSpace ℝ (Fin (n + 1)))
    (he : ipGram e = gram (n + 1) c) (hf : ipGram f = gram (n + 1) c) :
    ∃ T : EuclideanSpace ℝ (Fin (n + 1)) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin (n + 1)), ∀ i, T (e i) = f i
```

Reviewed by: ________  Date: ________  Faithful: yes / no / partly


## S02  (T2 and T3 (general n), done)

**Manuscript claim** (general n): T2: volume is at most 1, with equality only for the unit cube; T3: the cube is the unique maximizer and unique critical point of the volume

**Notes:** Squared volume statements, and the Euclidean link: the Lebesgue measure of the parallelotope squares to the Gram determinant (volume_sq_eq_det), so vol2 n c is the squared Euclidean volume.

```lean
theorem vol2_le_one {n : ℕ} {c : ℝ} (hlo : -1 < n * c) (hhi : c < 1) :
    vol2 n c ≤ 1
```

```lean
theorem vol2_eq_one_iff {n : ℕ} (hn : 1 ≤ n) {c : ℝ} (hlo : -1 < n * c) (hhi : c < 1) :
    vol2 n c = 1 ↔ c = 0
```

```lean
theorem deriv_vol2_eq_zero_iff {n : ℕ} (hn : 1 ≤ n) {c : ℝ} (hhi : c < 1) :
    deriv (vol2 n) c = 0 ↔ c = 0
```

```lean
theorem hasDerivAt_vol2 (n : ℕ) (c : ℝ) :
    HasDerivAt (vol2 n) (-(n : ℝ) * (n + 1) * c * (1 - c) ^ (n - 1)) c
```

```lean
theorem det_gram (n : ℕ) (c : ℝ) : (gram (n + 1) c).det = vol2 n c
```

```lean
theorem volume_sq_eq_det {d : ℕ} (e : Fin d → EuclideanSpace ℝ (Fin d)) :
    ((volume (parallelepiped e)).toReal) ^ 2 = (ipGram e).det
```

```lean
theorem volume_sq_rhombus {n : ℕ} {c : ℝ} (e : Fin (n + 1) → EuclideanSpace ℝ (Fin (n + 1)))
    (he : ipGram e = gram (n + 1) c) :
    ((MeasureTheory.volume (parallelepiped e)).toReal) ^ 2 = vol2 n c
```

```lean
theorem volume_rhombus_le_one {n : ℕ} {c : ℝ} (hlo : -1 < n * c) (hhi : c < 1)
    (e : Fin (n + 1) → EuclideanSpace ℝ (Fin (n + 1))) (he : ipGram e = gram (n + 1) c) :
    (MeasureTheory.volume (parallelepiped e)).toReal ≤ 1
```

Reviewed by: ________  Date: ________  Faithful: yes / no / partly


## S03  (T4 (general n), done)

**Manuscript claim** (general n): T4: second and third order expansion of the log volume at the cube

**Notes:** Cubic Taylor polynomial of log vol2 at c = 0 with explicit error bound (2n + 2n^4) c^4 for |c| <= 1/(2(n+1)), and the O(c^4) corollary.

```lean
theorem log_vol2_expansion (n : ℕ) {c : ℝ} (hc : |c| ≤ 1 / (2 * (n + 1))) :
    |Real.log (vol2 n c) - logExp n c| ≤ (2 * n + 2 * (n : ℝ) ^ 4) * c ^ 4
```

```lean
theorem log_vol2_isBigO (n : ℕ) :
    (fun c => Real.log (vol2 n c) - logExp n c) =O[nhds 0] fun c => c ^ 4
```

Reviewed by: ________  Date: ________  Faithful: yes / no / partly


## S04  (T5 (general n), done)

**Manuscript claim** (general n): T5: rank of the edge system at interior and endpoint values of the parameter

**Notes:** Dimension of the span of the edge vectors: n+1 in the interior, 1 at c = 1, n at c = -1/n, via rank of family = rank of Gram matrix.

```lean
theorem rank_gram_of_det_ne {n : ℕ} {c : ℝ} (h : c ≠ 1) (h' : 1 + n * c ≠ 0) :
    (gram (n + 1) c).rank = n + 1
```

```lean
theorem rank_interior {n : ℕ} {c : ℝ} (hlo : -1 < n * c) (hhi : c < 1) :
    (gram (n + 1) c).rank = n + 1
```

```lean
theorem rank_upper (n : ℕ) : (gram (n + 1) 1).rank = 1
```

```lean
theorem rank_lower (m : ℕ) : (gram (m + 2) (-(1 : ℝ) / (m + 1))).rank = m + 1
```

```lean
theorem principal_gram {k d : ℕ} (h : k ≤ d) (c : ℝ) :
    (gram d c).submatrix (Fin.castLE h) (Fin.castLE h) = gram k c
```

```lean
theorem finrank_span_eq_rank_ipGram (e : Fin d → EuclideanSpace ℝ (Fin d)) :
    Module.finrank ℝ (Submodule.span ℝ (Set.range e)) = (ipGram e).rank
```

```lean
theorem span_dim_interior {n : ℕ} {c : ℝ} (hlo : -1 < n * c) (hhi : c < 1)
    (e : Fin (n + 1) → EuclideanSpace ℝ (Fin (n + 1))) (he : ipGram e = gram (n + 1) c) :
    Module.finrank ℝ (Submodule.span ℝ (Set.range e)) = n + 1
```

```lean
theorem span_dim_upper {n : ℕ} (e : Fin (n + 1) → EuclideanSpace ℝ (Fin (n + 1)))
    (he : ipGram e = gram (n + 1) 1) :
    Module.finrank ℝ (Submodule.span ℝ (Set.range e)) = 1
```

```lean
theorem span_dim_lower {m : ℕ} (e : Fin (m + 2) → EuclideanSpace ℝ (Fin (m + 2)))
    (he : ipGram e = gram (m + 2) (-(1 : ℝ) / (m + 1))) :
    Module.finrank ℝ (Submodule.span ℝ (Set.range e)) = m + 1
```

Reviewed by: ________  Date: ________  Faithful: yes / no / partly


## S05  (T6 (general n), done)

**Manuscript claim** (general n): T6: facets are lower dimensional members of the family, and the boundary determines the parameter exactly when n is at least 3

**Notes:** Facets are lower dimensional members of the family. Geometric rigidity: if an isometry of R^(m+3) carries the rhombus with parameter c onto the rhombus with parameter s then c = s (via: extreme points of a parallelotope are its vertices; an isometry sends edges to signed edges). In dimension 2, R_2(c) and R_2(-c) are congruent by a translation (congruent_two_neg).

```lean
theorem facet_gram (d : ℕ) (c : ℝ) :
    (gram (d + 1) c).submatrix Fin.castSucc Fin.castSucc = gram d c
```

```lean
theorem vertex_lemma {n : ℕ} {c s : ℝ} (ε : Fin (n + 3) → ℝ)
    (hε : ∀ i, ε i = 1 ∨ ε i = -1)
    (h : ∀ i j, i ≠ j → ε i * ε j * c = s) : s = c
```

```lean
theorem cornerSet_eq_iff {d : ℕ} {c s : ℝ} :
    cornerSet (d + 3) c = cornerSet (d + 3) s ↔ c = s
```

```lean
theorem cornerSet_two_neg (c : ℝ) : cornerSet 2 c = cornerSet 2 (-c)
```

```lean
theorem extremePoints_parallelepiped (e : Fin d → V d) (h : LinearIndependent ℝ e) :
    extremePoints ℝ (parallelepiped e) = basisEquiv e h '' cubeVerts d
```

```lean
theorem edge_to_signed_edge (e f : Fin d → V d) (he : LinearIndependent ℝ e)
    (hf : LinearIndependent ℝ f) (T : V d ≃ᵃⁱ[ℝ] V d) (hT : T '' parallelepiped e = parallelepiped f)
    (i : Fin d) :
    ∃ j, ∃ σ : ℝ, (σ = 1 ∨ σ = -1) ∧ T.linearIsometryEquiv (e i) = σ • f j
```

```lean
theorem congruent_rhombi_param_eq {m : ℕ} {c s : ℝ}
    (hlo : -1 < ((m + 2 : ℕ) : ℝ) * c) (hhi : c < 1)
    (hlo' : -1 < ((m + 2 : ℕ) : ℝ) * s) (hhi' : s < 1)
    (e f : Fin (m + 3) → V (m + 3))
    (he : ipGram e = gram (m + 3) c) (hf : ipGram f = gram (m + 3) s)
    (T : V (m + 3) ≃ᵃⁱ[ℝ] V (m + 3)) (hT : T '' parallelepiped e = parallelepiped f) :
    c = s
```

```lean
theorem congruent_two_neg (e : Fin 2 → V 2) :
    ∃ T : V 2 ≃ᵃⁱ[ℝ] V 2, T '' parallelepiped (flip2 e) = parallelepiped e
```

Reviewed by: ________  Date: ________  Faithful: yes / no / partly


## S06  (T7 (general n), done)

**Manuscript claim** (general n): T7: exact value of det G_n(a/n) and its limit (1+a)exp(-a)

**Notes:** Dimension d = n + 1 and c = a / d, so vol2 n (a / (n + 1)) tends to (1 + a) exp(-a).

```lean
theorem tendsto_vol2 (a : ℝ) :
    Tendsto (fun n : ℕ => vol2 n (a / (n + 1))) atTop (𝓝 ((1 + a) * Real.exp (-a)))
```

Reviewed by: ________  Date: ________  Faithful: yes / no / partly


## S07  (T8 (n >= 3), done (fibre count))

**Manuscript claim** (general n): T8: volume takes each value in (0,1) exactly twice, with shape consequences that depend on n

**Notes:** Exactly one solution on each side of c = 0. The non-congruence consequence is congruent_rhombi_param_eq (see S05).

```lean
theorem vol2_two_fibres {n : ℕ} (hn : 1 ≤ n) {v : ℝ} (hv0 : 0 < v) (hv1 : v < 1) :
    (∃! c, c ∈ Set.Ioo (-(1 : ℝ) / n) 0 ∧ vol2 n c = v) ∧
    (∃! c, c ∈ Set.Ioo (0 : ℝ) 1 ∧ vol2 n c = v)
```

```lean
theorem vol2_strictMonoOn {n : ℕ} (hn : 1 ≤ n) :
    StrictMonoOn (vol2 n) (Set.Icc (-(1 : ℝ) / n) 0)
```

```lean
theorem vol2_strictAntiOn {n : ℕ} (hn : 1 ≤ n) :
    StrictAntiOn (vol2 n) (Set.Icc (0 : ℝ) 1)
```

Reviewed by: ________  Date: ________  Faithful: yes / no / partly


## S08  (T8 (n = 2), done)

**Manuscript claim** (n = 2 only): T8: volume takes each value in (0,1) exactly twice, with shape consequences that depend on n (in dimension 2 the partner of c is -c, and R_2(c), R_2(-c) are congruent)

**Notes:** Flipping one edge sends c to -c and maps the parallelogram to a translate of itself (congruence). flipGram_not_member shows the same flip leaves the family for d >= 3 when c is nonzero.

```lean
theorem vol2_two_fibres {n : ℕ} (hn : 1 ≤ n) {v : ℝ} (hv0 : 0 < v) (hv1 : v < 1) :
    (∃! c, c ∈ Set.Ioo (-(1 : ℝ) / n) 0 ∧ vol2 n c = v) ∧
    (∃! c, c ∈ Set.Ioo (0 : ℝ) 1 ∧ vol2 n c = v)
```

```lean
theorem ipGram_flip2 {c : ℝ} (e : Fin 2 → EuclideanSpace ℝ (Fin 2))
    (he : ipGram e = gram 2 c) : ipGram (flip2 e) = gram 2 (-c)
```

```lean
theorem parallelepiped_flip2 {E : Type*} [AddCommGroup E] [Module ℝ E] (e : Fin 2 → E) :
    (fun x => x + e 1) '' parallelepiped (flip2 e) = parallelepiped e
```

```lean
theorem flipGram_two (c : ℝ) : flipGram 2 1 c = gram 2 (-c)
```

```lean
theorem flipGram_not_member {d : ℕ} {c : ℝ} (hc : c ≠ 0) (s : ℝ) :
    flipGram (d + 3) 2 c ≠ gram (d + 3) s
```

Reviewed by: ________  Date: ________  Faithful: yes / no / partly


## S09  (T1 (infinite), done)

**Manuscript claim** (infinite dimension): T1: unit vector systems with equal inner products exist for 0 <= c <= 1, and the Gram operator is bounded on l2 only for c = 0

**Notes:** Unit vectors in l2 with common inner product c exist for 0 <= c <= 1. For c != 0 no column of the infinite Gram matrix is square summable, so no operator on l2 has that matrix; for c = 0 the matrix is the identity. The finite-section unboundedness is also proved.

```lean
theorem sysVec_isSystem {c : ℝ} (h0 : 0 ≤ c) (h1 : c ≤ 1) : IsSystem (sysVec c) c
```

```lean
theorem gram_form_unbounded {c : ℝ} (hc : 0 < c) (M : ℝ) :
    ∃ n : ℕ, M * ((n : ℝ) + 1) <
      (fun _ : Fin (n + 1) => (1 : ℝ)) ⬝ᵥ (gram (n + 1) c).mulVec (fun _ => 1)
```

```lean
theorem gramCol_not_mem_l2 {c : ℝ} (hc : c ≠ 0) (j : ℕ) : ¬ Memℓp (gramCol c j) 2
```

```lean
theorem no_gram_operator {c : ℝ} (hc : c ≠ 0) :
    ¬ ∃ T : lp (fun _ : ℕ => ℝ) 2 →ₗ[ℝ] lp (fun _ : ℕ => ℝ) 2,
      ∀ i j, (T (lp.single 2 j (1 : ℝ))) i = gramCol c j i
```

```lean
theorem gram_operator_zero :
    ∃ T : lp (fun _ : ℕ => ℝ) 2 →L[ℝ] lp (fun _ : ℕ => ℝ) 2,
      ∀ i j, (T (lp.single 2 j (1 : ℝ))) i = gramCol 0 j i
```

Reviewed by: ________  Date: ________  Faithful: yes / no / partly


## S10  (T2 and T3 (infinite), done)

**Manuscript claim** (infinite dimension): T2: limiting volume is 1 at c = 0 and 0 for 0 < c < 1; T3: the cube is the unique maximizer of the limiting volume

**Notes:** Limiting volume is 0 for 0 < c < 1 and 1 at c = 0, so the cube is the unique maximizer of the limiting volume.

```lean
theorem tendsto_vol2_zero {c : ℝ} (h0 : 0 < c) (h1 : c < 1) :
    Tendsto (fun n : ℕ => vol2 n c) atTop (𝓝 0)
```

```lean
theorem limit_volume_eq_one {c ℓ : ℝ} (h0 : 0 ≤ c) (h1 : c < 1)
    (hl : Tendsto (fun n : ℕ => vol2 n c) atTop (𝓝 ℓ)) (hℓ : ℓ = 1) : c = 0
```

Reviewed by: ________  Date: ________  Faithful: yes / no / partly


## S11  (T4 (infinite), done)

**Manuscript claim** (infinite dimension): T4: the quadratic coefficient of the log volume diverges with the dimension

**Notes:** The quadratic coefficient -n(n+1)/2 of the log volume (see log_vol2_expansion) tends to -infinity.

```lean
theorem quadratic_coeff_diverges :
    Tendsto (fun n : ℕ => -((n : ℝ) * (n + 1) / 2)) atTop atBot
```

Reviewed by: ________  Date: ________  Faithful: yes / no / partly


## S12  (T5 (infinite), done)

**Manuscript claim** (infinite dimension): T5: for 0 <= c < 1 the system is linearly independent and fits in no finite dimensional space

**Notes:** For 0 <= c < 1 every infinite system is linearly independent and lies in no finite dimensional subspace.

```lean
theorem system_linearIndependent {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {e : ℕ → E} {c : ℝ} (he : IsSystem e c) (h0 : 0 ≤ c) (h1 : c < 1) :
    LinearIndependent ℝ e
```

```lean
theorem system_not_finite_dim {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {e : ℕ → E} {c : ℝ} (he : IsSystem e c) (h0 : 0 ≤ c) (h1 : c < 1)
    (W : Submodule ℝ E) (hW : ∀ i, e i ∈ W) : ¬ FiniteDimensional ℝ W
```

Reviewed by: ________  Date: ________  Faithful: yes / no / partly


## S13  (T6 (infinite), done)

**Manuscript claim** (infinite dimension): T6: for every finite section of order at least 3 the boundary determines c

**Notes:** The geometric rigidity theorem is stated for every dimension m+3 >= 3, hence for every finite section of order at least 3.

```lean
theorem congruent_rhombi_param_eq {m : ℕ} {c s : ℝ}
    (hlo : -1 < ((m + 2 : ℕ) : ℝ) * c) (hhi : c < 1)
    (hlo' : -1 < ((m + 2 : ℕ) : ℝ) * s) (hhi' : s < 1)
    (e f : Fin (m + 3) → V (m + 3))
    (he : ipGram e = gram (m + 3) c) (hf : ipGram f = gram (m + 3) s)
    (T : V (m + 3) ≃ᵃⁱ[ℝ] V (m + 3)) (hT : T '' parallelepiped e = parallelepiped f) :
    c = s
```

```lean
theorem cornerSet_eq_iff {d : ℕ} {c s : ℝ} :
    cornerSet (d + 3) c = cornerSet (d + 3) s ↔ c = s
```

```lean
theorem flipGram_not_member {d : ℕ} {c : ℝ} (hc : c ≠ 0) (s : ℝ) :
    flipGram (d + 3) 2 c ≠ gram (d + 3) s
```

Reviewed by: ________  Date: ________  Faithful: yes / no / partly


## S14  (T8 (infinite), done)

**Manuscript claim** (infinite dimension): T8: the limiting volume is constant on (0,1), so volume does not determine c

**Notes:** Two distinct parameters in (0,1) have the same limiting volume 0.

```lean
theorem limit_volume_not_injective :
    ∃ c c' : ℝ, c ≠ c' ∧ 0 < c ∧ c < 1 ∧ 0 < c' ∧ c' < 1 ∧
      Tendsto (fun n : ℕ => vol2 n c) atTop (𝓝 0) ∧
      Tendsto (fun n : ℕ => vol2 n c') atTop (𝓝 0)
```

Reviewed by: ________  Date: ________  Faithful: yes / no / partly
