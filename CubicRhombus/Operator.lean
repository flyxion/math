import Mathlib
import CubicRhombus.Infinite

/-!
# S09, operator form: the infinite Gram matrix defines an operator on `ℓ²` only when `c = 0`

The infinite Gram matrix has columns `(c, ..., c, 1, c, ...)`.  For `c ≠ 0` no column is square
summable, so no operator on `ℓ²` (bounded or not, defined on the unit vectors) can have that
matrix.  For `c = 0` the matrix is the identity.
-/

open Filter
open scoped ENNReal

namespace CubicRhombus

/-- The `j`-th column of the infinite Gram matrix. -/
def gramCol (c : ℝ) (j : ℕ) : ℕ → ℝ := fun i => if i = j then 1 else c

theorem gramCol_not_mem_l2 {c : ℝ} (hc : c ≠ 0) (j : ℕ) : ¬ Memℓp (gramCol c j) 2 := by
  intro h
  have hs : Summable fun i => ‖gramCol c j i‖ ^ (2 : ℝ≥0∞).toReal :=
    (memℓp_gen_iff (by norm_num)).mp h
  have hs' := (summable_nat_add_iff (j + 1)).mpr hs
  have : (fun i => ‖gramCol c j (i + (j + 1))‖ ^ (2 : ℝ≥0∞).toReal) = fun _ => c ^ 2 := by
    funext i
    have : i + (j + 1) ≠ j := by omega
    simp [gramCol, this]
  rw [this] at hs'
  exact hc (pow_eq_zero_iff (two_ne_zero) |>.mp ((summable_const_iff _).mp hs'))

/-- **S09, operator form.**  For `c ≠ 0` there is no linear operator on `ℓ²` whose matrix in the
standard basis is the infinite Gram matrix. -/
theorem no_gram_operator {c : ℝ} (hc : c ≠ 0) :
    ¬ ∃ T : lp (fun _ : ℕ => ℝ) 2 →ₗ[ℝ] lp (fun _ : ℕ => ℝ) 2,
      ∀ i j, (T (lp.single 2 j (1 : ℝ))) i = gramCol c j i := by
  rintro ⟨T, hT⟩
  apply gramCol_not_mem_l2 hc 0
  have := (T (lp.single 2 0 (1 : ℝ))).2
  have e : (fun i => (T (lp.single 2 0 (1 : ℝ))) i) = gramCol c 0 := funext fun i => hT i 0
  rw [← e]; exact this

/-- For `c = 0` the matrix is the identity, which is a bounded operator. -/
theorem gram_operator_zero :
    ∃ T : lp (fun _ : ℕ => ℝ) 2 →L[ℝ] lp (fun _ : ℕ => ℝ) 2,
      ∀ i j, (T (lp.single 2 j (1 : ℝ))) i = gramCol 0 j i := by
  refine ⟨ContinuousLinearMap.id ℝ _, fun i j => ?_⟩
  by_cases h : i = j
  · subst h; simp [gramCol, lp.single_apply]
  · simp [gramCol, lp.single_apply, h]

end CubicRhombus
