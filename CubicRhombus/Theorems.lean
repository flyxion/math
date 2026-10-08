import Mathlib
import CubicRhombus.Gram

/-!
# Statement classes of the cubic rhombus corpus

Lean proofs of the propositions carried by the manuscripts, for the finite dimensional classes.
Dimension is `d = n + 1`.  Every theorem here is about the Gram matrix `(1 - c) I + c J`
(see `Gram.lean`).  Human review of the *statements* (do they say what the manuscripts say?)
is still required: Lean checks the proofs, not the translation.
-/

open Matrix Filter Topology

namespace CubicRhombus

/-! ## T3: unique critical point -/

theorem deriv_vol2_eq_zero_iff {n : ℕ} (hn : 1 ≤ n) {c : ℝ} (hhi : c < 1) :
    deriv (vol2 n) c = 0 ↔ c = 0 := by
  rw [(hasDerivAt_vol2 n c).deriv]
  have h1 : (1 - c) ^ (n - 1) ≠ 0 := pow_ne_zero _ (by linarith)
  have hn' : (n : ℝ) ≠ 0 := by positivity
  have hn1 : (n : ℝ) + 1 ≠ 0 := by positivity
  constructor
  · intro h
    have : (-(n : ℝ) * (n + 1) * c) * (1 - c) ^ (n - 1) = 0 := by linarith
    rcases mul_eq_zero.mp this with h2 | h2
    · simpa [hn', hn1] using h2
    · exact absurd h2 h1
  · rintro rfl; simp

/-! ## T8: each value in (0,1) is taken exactly twice -/

theorem vol2_strictMonoOn {n : ℕ} (hn : 1 ≤ n) :
    StrictMonoOn (vol2 n) (Set.Icc (-(1 : ℝ) / n) 0) := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  apply strictMonoOn_of_deriv_pos (convex_Icc _ _)
  · exact (continuous_iff_continuousAt.2 fun x => (hasDerivAt_vol2 n x).continuousAt).continuousOn
  · intro x hx
    rw [interior_Icc] at hx
    rw [(hasDerivAt_vol2 n x).deriv]
    have h1 : 0 < (1 - x) ^ (n - 1) := pow_pos (by linarith [hx.2]) _
    have hpos : 0 < (n : ℝ) * (n + 1) := by positivity
    have : 0 < (n : ℝ) * (n + 1) * (-x) := mul_pos hpos (neg_pos.mpr hx.2)
    have h2 : 0 < -(n : ℝ) * (n + 1) * x := by linarith
    exact mul_pos h2 h1

theorem vol2_strictAntiOn {n : ℕ} (hn : 1 ≤ n) :
    StrictAntiOn (vol2 n) (Set.Icc (0 : ℝ) 1) := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  apply strictAntiOn_of_deriv_neg (convex_Icc _ _)
  · exact (continuous_iff_continuousAt.2 fun x => (hasDerivAt_vol2 n x).continuousAt).continuousOn
  · intro x hx
    rw [interior_Icc] at hx
    rw [(hasDerivAt_vol2 n x).deriv]
    have h1 : 0 < (1 - x) ^ (n - 1) := pow_pos (by linarith [hx.2]) _
    have : (n : ℝ) * (n + 1) * x > 0 := by have := hx.1; positivity
    nlinarith

lemma vol2_zero (n : ℕ) : vol2 n 0 = 1 := by simp [vol2]
lemma vol2_one {n : ℕ} (hn : 1 ≤ n) : vol2 n 1 = 0 := by
  unfold vol2
  rw [sub_self, zero_pow (show n ≠ 0 by omega), zero_mul]
lemma vol2_lower {n : ℕ} (hn : 1 ≤ n) : vol2 n (-(1 : ℝ) / n) = 0 := by
  have hn0 : (n : ℝ) ≠ 0 := by positivity
  have h : (n : ℝ) * (-(1 : ℝ) / n) = -1 := by field_simp
  unfold vol2
  rw [h]
  norm_num

/-- **T8.**  For every `v` in `(0, 1)` the volume polynomial takes the value `v` exactly once in
`(-1/n, 0)` and exactly once in `(0, 1)`.  So volume does not determine `c`. -/
theorem vol2_two_fibres {n : ℕ} (hn : 1 ≤ n) {v : ℝ} (hv0 : 0 < v) (hv1 : v < 1) :
    (∃! c, c ∈ Set.Ioo (-(1 : ℝ) / n) 0 ∧ vol2 n c = v) ∧
    (∃! c, c ∈ Set.Ioo (0 : ℝ) 1 ∧ vol2 n c = v) := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hcont : Continuous (vol2 n) :=
    continuous_iff_continuousAt.2 fun x => (hasDerivAt_vol2 n x).continuousAt
  have hlo : -(1 : ℝ) / n < 0 := by
    have : 0 < (1 : ℝ) / n := by positivity
    linarith [show -(1 : ℝ) / n = -(1 / n) by ring]
  refine ⟨?_, ?_⟩
  · have hex : v ∈ vol2 n '' Set.Ioo (-(1 : ℝ) / n) 0 :=
      intermediate_value_Ioo hlo.le hcont.continuousOn
        (by rw [vol2_lower hn, vol2_zero]; exact ⟨hv0, hv1⟩)
    obtain ⟨c, hc, hcv⟩ := hex
    refine ⟨c, ⟨hc, hcv⟩, ?_⟩
    rintro y ⟨hy, hyv⟩
    exact (vol2_strictMonoOn hn).injOn (Set.Ioo_subset_Icc_self hy)
      (Set.Ioo_subset_Icc_self hc) (hyv.trans hcv.symm)
  · have hex : v ∈ vol2 n '' Set.Ioo (0 : ℝ) 1 :=
      intermediate_value_Ioo' zero_le_one hcont.continuousOn
        (by rw [vol2_zero, vol2_one hn]; exact ⟨hv0, hv1⟩)
    obtain ⟨c, hc, hcv⟩ := hex
    refine ⟨c, ⟨hc, hcv⟩, ?_⟩
    rintro y ⟨hy, hyv⟩
    exact (vol2_strictAntiOn hn).injOn (Set.Ioo_subset_Icc_self hy)
      (Set.Ioo_subset_Icc_self hc) (hyv.trans hcv.symm)

/-! ## T1: positive definiteness exactly on `(-1/n, 1)` -/

theorem quadForm_gram {d : ℕ} (c : ℝ) (x : Fin d → ℝ) :
    x ⬝ᵥ (gram d c).mulVec x = (1 - c) * ∑ i, x i ^ 2 + c * (∑ i, x i) ^ 2 := by
  have hJ : (Matrix.of fun (_ : Fin d) (_ : Fin d) => (1 : ℝ)).mulVec x = fun _ => ∑ j, x j := by
    ext i; simp [mulVec, dotProduct]
  have h1 : x ⬝ᵥ x = ∑ i, x i ^ 2 := by simp [dotProduct, sq]
  have h2 : x ⬝ᵥ (fun _ : Fin d => ∑ j, x j) = (∑ i, x i) ^ 2 := by
    simp [dotProduct, ← Finset.sum_mul, sq]
  rw [gram_eq, add_mulVec, smul_mulVec, one_mulVec, smul_mulVec, hJ, dotProduct_add,
    dotProduct_smul, dotProduct_smul, h1, h2]
  simp only [smul_eq_mul]

theorem quadForm_gram_pos {n : ℕ} {c : ℝ} (hlo : -1 < n * c) (hhi : c < 1)
    {x : Fin (n + 1) → ℝ} (hx : x ≠ 0) : 0 < x ⬝ᵥ (gram (n + 1) c).mulVec x := by
  rw [quadForm_gram]
  have hS : 0 < ∑ i, x i ^ 2 := by
    obtain ⟨i, hi⟩ := Function.ne_iff.1 hx
    have hi' : x i ≠ 0 := by simpa using hi
    have hxi : 0 < x i ^ 2 := by positivity
    exact lt_of_lt_of_le hxi (Finset.single_le_sum (f := fun i => x i ^ 2)
      (fun j _ => sq_nonneg _) (Finset.mem_univ i))
  by_cases hc : 0 ≤ c
  · have : 0 ≤ c * (∑ i, x i) ^ 2 := by positivity
    nlinarith
  · have hc : c < 0 := not_le.mp hc
    have hcs : (∑ i, x i) ^ 2 ≤ (n + 1 : ℕ) * ∑ i, x i ^ 2 := by
      simpa using sq_sum_le_card_mul_sum_sq (s := Finset.univ) (f := x)
    have h2 : c * ((n + 1 : ℕ) * ∑ i, x i ^ 2) ≤ c * (∑ i, x i) ^ 2 :=
      mul_le_mul_of_nonpos_left hcs hc.le
    have h3 : 0 < (1 + n * c) * ∑ i, x i ^ 2 := mul_pos (by linarith) hS
    push_cast at h2
    nlinarith

/-- Outside the interval the Gram matrix is not positive definite. -/
theorem not_pos_of_le {n : ℕ} (hn : 1 ≤ n) {c : ℝ} (h : c ≤ -1 / n ∨ 1 ≤ c) :
    ∃ x : Fin (n + 1) → ℝ, x ≠ 0 ∧ x ⬝ᵥ (gram (n + 1) c).mulVec x ≤ 0 := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  rcases h with h | h
  · refine ⟨fun _ => 1, fun h0 => ?_, ?_⟩
    · have := congrFun h0 0; simp at this
    · rw [quadForm_gram]
      have : (n : ℝ) * c ≤ -1 := by
        have := mul_le_mul_of_nonneg_left h hn'.le
        rwa [mul_div_cancel₀ _ hn'.ne'] at this
      simp
      nlinarith
  · obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    refine ⟨Fin.cons 1 (Fin.cons (-1) (fun _ => 0)), fun h0 => ?_, ?_⟩
    · have := congrFun h0 0; simp at this
    · rw [quadForm_gram]
      simp [Fin.sum_univ_succ]
      linarith

/-- **T1 (positivity range).**  The Gram matrix of `n + 1` unit vectors with common inner product
`c` is positive definite exactly when `-1/n < c < 1` (stated as `-1 < n c`), for `n ≥ 1`. -/
theorem posdef_iff {n : ℕ} (hn : 1 ≤ n) {c : ℝ} :
    (∀ x : Fin (n + 1) → ℝ, x ≠ 0 → 0 < x ⬝ᵥ (gram (n + 1) c).mulVec x) ↔
      (-1 < n * c ∧ c < 1) := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  constructor
  · intro h
    by_contra hneg
    have hcase : c ≤ -1 / n ∨ 1 ≤ c := by
      rcases not_and_or.mp hneg with h1 | h1
      · left
        rw [le_div_iff₀ hn']
        linarith [not_lt.mp h1]
      · right; exact not_lt.mp h1
    obtain ⟨x, hx, hle⟩ := not_pos_of_le hn hcase
    exact absurd (h x hx) (not_lt.mpr hle)
  · rintro ⟨h1, h2⟩ x hx
    exact quadForm_gram_pos h1 h2 hx

/-! ## T7: the limit `det G_d(a / d) → (1 + a) e^{-a}` -/

theorem tendsto_vol2 (a : ℝ) :
    Tendsto (fun n : ℕ => vol2 n (a / (n + 1))) atTop (𝓝 ((1 + a) * Real.exp (-a))) := by
  have hf := Real.tendsto_one_add_div_pow_exp (-a)
  have hg : Tendsto (fun n : ℕ => (1 + (-a) / ((n + 1 : ℕ) : ℝ)) ^ (n + 1)) atTop
      (𝓝 (Real.exp (-a))) :=
    (tendsto_add_atTop_iff_nat (f := fun m : ℕ => (1 + (-a) / (m : ℝ)) ^ m) 1).2 hf
  have h0 : Tendsto (fun n : ℕ => a / ((n : ℝ) + 1)) atTop (𝓝 0) := by
    have := (tendsto_add_atTop_iff_nat (f := fun m : ℕ => a / (m : ℝ)) 1).2
      (tendsto_const_div_atTop_nhds_zero_nat a)
    simpa using this
  have hq : Tendsto (fun n : ℕ => 1 - a / ((n : ℝ) + 1)) atTop (𝓝 1) := by
    simpa using (tendsto_const_nhds (x := (1 : ℝ))).sub h0
  have hr : Tendsto (fun n : ℕ => 1 + (n : ℝ) * (a / ((n : ℝ) + 1))) atTop (𝓝 (1 + a)) := by
    have : Tendsto (fun n : ℕ => 1 + a - a / ((n : ℝ) + 1)) atTop (𝓝 (1 + a - 0)) :=
      (tendsto_const_nhds (x := 1 + a)).sub h0
    rw [sub_zero] at this
    refine this.congr (fun n => ?_)
    have : ((n : ℝ) + 1) ≠ 0 := by positivity
    field_simp
    ring
  have hmain := (hg.div hq one_ne_zero).mul hr
  have hev : ∀ᶠ n : ℕ in atTop, 1 - a / ((n : ℝ) + 1) ≠ 0 := hq.eventually_ne one_ne_zero
  have key : (fun n : ℕ => (1 + (-a) / ((n + 1 : ℕ) : ℝ)) ^ (n + 1) / (1 - a / ((n : ℝ) + 1)) *
      (1 + (n : ℝ) * (a / ((n : ℝ) + 1)))) =ᶠ[atTop] fun n : ℕ => vol2 n (a / (n + 1)) := by
    filter_upwards [hev] with n hn
    have e : 1 + (-a) / ((n + 1 : ℕ) : ℝ) = 1 - a / ((n : ℝ) + 1) := by push_cast; ring
    rw [e, pow_succ, mul_div_cancel_right₀ _ hn]
    rfl
  have := hmain.congr' key
  convert this using 2
  ring

/-! ## T6: vertex Gram matrices (the rigidity lemma) -/

private lemma fin_ne02 (n : ℕ) : (0 : Fin (n + 3)) ≠ 2 := by
  intro h
  have := congrArg Fin.val h
  rw [Fin.val_zero, Fin.val_two] at this
  omega

private lemma fin_ne12 (n : ℕ) : (1 : Fin (n + 3)) ≠ 2 := by
  intro h
  have := congrArg Fin.val h
  rw [Fin.val_one, Fin.val_two] at this
  omega

theorem vertex_lemma {n : ℕ} {c s : ℝ} (ε : Fin (n + 3) → ℝ)
    (hε : ∀ i, ε i = 1 ∨ ε i = -1)
    (h : ∀ i j, i ≠ j → ε i * ε j * c = s) : s = c := by
  have h01 := h 0 1 (by simp)
  have h02 := h 0 2 (fin_ne02 n)
  have h12 := h 1 2 (fin_ne12 n)
  rcases hε 0 with h0 | h0 <;> rcases hε 1 with h1 | h1 <;> rcases hε 2 with h2 | h2 <;>
    simp [h0, h1, h2] at h01 h02 h12 <;> linarith

/-- In dimension 2 the lemma fails: the vertex with `ε = (1, -1)` has off-diagonal entry `-c`. -/
example (c : ℝ) (hc : c ≠ 0) : ¬ (-c = c) := by
  intro h; apply hc; linarith

end CubicRhombus
