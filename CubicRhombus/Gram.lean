import Mathlib

/-!
# The cubic rhombus: Gram matrix, volume, facets

A *cubic rhombus* `R_d(c)` is the parallelotope spanned by `d` unit vectors whose pairwise
inner products all equal `c`.  Everything in the corpus is computed from its Gram matrix

  `G_d(c) = (1 - c) I + c J`,

where `J` is the all ones matrix.  Dimension is written `d = n + 1` throughout this file so that
`d - 1 = n` needs no natural number subtraction.
-/

open Matrix

namespace CubicRhombus

/-- Gram matrix of `d` unit vectors with all pairwise inner products equal to `c`. -/
def gram (d : ℕ) (c : ℝ) : Matrix (Fin d) (Fin d) ℝ :=
  Matrix.of fun i j => if i = j then 1 else c

/-- The determinant polynomial `(1 - c)^n (1 + n c)`, the squared volume in dimension `n + 1`. -/
noncomputable def vol2 (n : ℕ) (c : ℝ) : ℝ := (1 - c) ^ n * (1 + n * c)

lemma gram_eq (d : ℕ) (c : ℝ) :
    gram d c = (1 - c) • (1 : Matrix (Fin d) (Fin d) ℝ) +
      c • (Matrix.of fun _ _ => (1 : ℝ)) := by
  ext i j
  by_cases h : i = j
  · subst h; simp [gram]
  · simp [gram, h, Matrix.one_apply_ne h]

/-- **Lemma 1 (volume).**  `det G_{n+1}(c) = (1 - c)^n (1 + n c)`, for every real `c`. -/
theorem det_gram (n : ℕ) (c : ℝ) : (gram (n + 1) c).det = vol2 n c := by
  unfold vol2
  by_cases hc : c = 1
  · subst hc
    cases n with
    | zero => simp [gram]
    | succ m =>
      have hrows : (gram (m + 2) 1) 0 = (gram (m + 2) 1) 1 := by
        ext j; simp [gram]
      rw [Matrix.det_zero_of_row_eq (i := 0) (j := 1) (by simp) hrows]
      simp
  · have h1 : (1 - c) ≠ 0 := sub_ne_zero.mpr (Ne.symm hc)
    set u : Fin (n + 1) → ℝ := fun _ => c / (1 - c) with hu
    set v : Fin (n + 1) → ℝ := fun _ => 1 with hv
    have hG : gram (n + 1) c =
        (1 - c) • (1 + replicateCol Unit u * replicateRow Unit v) := by
      ext i j
      by_cases h : i = j
      · subst h
        simp [gram, hu, hv, Matrix.mul_apply]
        field_simp
        ring
      · simp [gram, h, hu, hv, Matrix.mul_apply, Matrix.one_apply_ne h]
        field_simp
    rw [hG, Matrix.det_smul, det_one_add_replicateCol_mul_replicateRow]
    simp [hu, hv, dotProduct]
    field_simp
    ring

/-- **Lemma 2 (facets).**  Deleting the last edge vector leaves the Gram matrix of the same family
in one dimension lower. -/
theorem facet_gram (d : ℕ) (c : ℝ) :
    (gram (d + 1) c).submatrix Fin.castSucc Fin.castSucc = gram d c := by
  ext i j
  simp [gram, Fin.castSucc_inj]

/-- The volume polynomial has the stated derivative. -/
theorem hasDerivAt_vol2 (n : ℕ) (c : ℝ) :
    HasDerivAt (vol2 n) (-(n : ℝ) * (n + 1) * c * (1 - c) ^ (n - 1)) c := by
  have h1 : HasDerivAt (fun x : ℝ => (1 - x) ^ n) (n * (1 - c) ^ (n - 1) * (-1)) c := by
    simpa using ((hasDerivAt_id c).const_sub 1).fun_pow n
  have h2 : HasDerivAt (fun x : ℝ => 1 + (n : ℝ) * x) (n : ℝ) c := by
    simpa using ((hasDerivAt_id c).const_mul (n : ℝ)).const_add 1
  have h3 := h1.mul h2
  show HasDerivAt (fun x : ℝ => (1 - x) ^ n * (1 + (n : ℝ) * x)) _ c
  convert h3 using 1
  cases n with
  | zero => simp
  | succ m =>
    simp only [Nat.add_sub_cancel, Nat.cast_add, Nat.cast_one, pow_succ]
    ring

private lemma log_vol2 {n : ℕ} {c : ℝ} (ha : 0 < 1 - c) (hb : 0 < 1 + n * c) :
    Real.log (vol2 n c) = n * Real.log (1 - c) + Real.log (1 + n * c) := by
  unfold vol2
  rw [Real.log_mul (pow_pos ha n).ne' hb.ne', Real.log_pow]

/-- **T2 (a sharp inequality), squared form.**  For `-1/n < c < 1` the volume is at most `1`,
with equality exactly at the cube `c = 0`. -/
theorem vol2_le_one {n : ℕ} {c : ℝ} (hlo : -1 < n * c) (hhi : c < 1) :
    vol2 n c ≤ 1 := by
  have ha : 0 < 1 - c := by linarith
  have hb : 0 < 1 + n * c := by linarith
  have h1 : Real.log (1 - c) ≤ -c := by
    have := Real.log_le_sub_one_of_pos ha; linarith
  have h2 : Real.log (1 + n * c) ≤ n * c := by
    have := Real.log_le_sub_one_of_pos hb; linarith
  have h3 : (n : ℝ) * Real.log (1 - c) ≤ n * (-c) :=
    mul_le_mul_of_nonneg_left h1 (Nat.cast_nonneg n)
  have hpos : 0 < vol2 n c := mul_pos (pow_pos ha n) hb
  have hlog : Real.log (vol2 n c) ≤ 0 := by
    rw [log_vol2 ha hb]; nlinarith
  exact (Real.log_nonpos_iff hpos.le).mp hlog

theorem vol2_eq_one_iff {n : ℕ} (hn : 1 ≤ n) {c : ℝ} (hlo : -1 < n * c) (hhi : c < 1) :
    vol2 n c = 1 ↔ c = 0 := by
  constructor
  · intro h
    by_contra hc
    have ha : 0 < 1 - c := by linarith
    have hb : 0 < 1 + n * c := by linarith
    have h1 : Real.log (1 - c) < -c := by
      have := Real.log_lt_sub_one_of_pos ha (by intro h'; apply hc; linarith); linarith
    have h2 : Real.log (1 + n * c) ≤ n * c := by
      have := Real.log_le_sub_one_of_pos hb; linarith
    have hn' : (0 : ℝ) < n := by exact_mod_cast hn
    have h3 : (n : ℝ) * Real.log (1 - c) < n * (-c) := mul_lt_mul_of_pos_left h1 hn'
    have hlog : Real.log (vol2 n c) < 0 := by
      rw [log_vol2 ha hb]; nlinarith
    rw [h, Real.log_one] at hlog
    exact lt_irrefl _ hlog
  · rintro rfl
    simp [vol2]

end CubicRhombus
