import Mathlib
import CubicRhombus.Gram
import CubicRhombus.Theorems

/-!
# S04 / T5: rank of the edge system

For `n + 1` edge vectors with Gram matrix `gram (n+1) c`, the rank is `n + 1` in the interior and for
every `c` outside `{1, -1/n}`, `n` at the lower endpoint `c = -1/n`, and `1` at the upper endpoint
`c = 1`.  (The rank of a family of vectors equals the rank of its Gram matrix.)
-/

namespace CubicRhombus

/-- Principal submatrices of the Gram matrix are Gram matrices of the initial sub-families. -/
theorem principal_gram {k d : ℕ} (h : k ≤ d) (c : ℝ) :
    (gram d c).submatrix (Fin.castLE h) (Fin.castLE h) = gram k c := by
  ext i j
  simp [gram, Fin.castLE_inj]

theorem rank_gram_of_det_ne {n : ℕ} {c : ℝ} (h : c ≠ 1) (h' : 1 + n * c ≠ 0) :
    (gram (n + 1) c).rank = n + 1 := by
  have hdet : (gram (n + 1) c).det ≠ 0 := by
    rw [det_gram]
    exact mul_ne_zero (pow_ne_zero _ (sub_ne_zero.mpr (Ne.symm h))) h'
  have := Matrix.rank_of_det_mem_nonZeroDivisors (A := gram (n + 1) c)
    (mem_nonZeroDivisors_of_ne_zero hdet)
  simpa using this

/-- **T5, interior.**  Full rank for all `c` other than the two endpoint values. -/
theorem rank_interior {n : ℕ} {c : ℝ} (hlo : -1 < n * c) (hhi : c < 1) :
    (gram (n + 1) c).rank = n + 1 :=
  rank_gram_of_det_ne (by linarith) (by linarith)

/-- **T5, upper endpoint.**  At `c = 1` all edge vectors coincide and the rank is `1`. -/
theorem rank_upper (n : ℕ) : (gram (n + 1) 1).rank = 1 := by
  apply le_antisymm
  · have h : gram (n + 1) 1 = Matrix.vecMulVec (fun _ => (1 : ℝ)) (fun _ => (1 : ℝ)) := by
      ext i j; simp [gram, Matrix.vecMulVec_apply]
    rw [h]; exact Matrix.rank_vecMulVec_le _ _
  · have h1 := Matrix.rank_submatrix_le (gram (n + 1) 1) (Fin.castLE (by omega : 1 ≤ n + 1))
      (Fin.castLE (by omega : 1 ≤ n + 1))
    rw [principal_gram] at h1
    have h2 : (gram 1 (1 : ℝ)).rank = 1 := by
      have : gram 1 (1 : ℝ) = 1 := by
        ext i j; fin_cases i; fin_cases j; simp [gram]
      rw [this, Matrix.rank_one]; simp
    omega

/-- **T5, lower endpoint.**  At `c = -1/(m+1)` the `m + 2` edge vectors span only `m + 1`
dimensions: the all-ones vector is in the kernel of the Gram matrix, and a principal minor is
nonzero. -/
theorem rank_lower (m : ℕ) : (gram (m + 2) (-(1 : ℝ) / (m + 1))).rank = m + 1 := by
  set c : ℝ := -(1 : ℝ) / (m + 1) with hc
  have hm : (0 : ℝ) < m + 1 := by positivity
  apply le_antisymm
  · -- the all-ones vector lies in the kernel
    have hker : (gram (m + 2) c).mulVec (fun _ => (1 : ℝ)) = 0 := by
      have hJ : (Matrix.of fun (_ : Fin (m + 2)) (_ : Fin (m + 2)) => (1 : ℝ)).mulVec
          (fun _ => (1 : ℝ)) = fun _ => ((m : ℝ) + 2) := by
        ext i; simp [Matrix.mulVec, dotProduct]
      rw [gram_eq, Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec,
        Matrix.smul_mulVec, hJ]
      ext i
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
      rw [hc]; field_simp; ring
    have hrn := LinearMap.finrank_range_add_finrank_ker (gram (m + 2) c).mulVecLin
    have hpos : 0 < Module.finrank ℝ (LinearMap.ker (gram (m + 2) c).mulVecLin) := by
      apply Module.finrank_pos_iff_exists_ne_zero.mpr
      refine ⟨⟨fun _ => (1 : ℝ), ?_⟩, ?_⟩
      · simpa [LinearMap.mem_ker] using hker
      · intro h
        have := congrArg (fun x : LinearMap.ker (gram (m + 2) c).mulVecLin => (x : Fin (m + 2) → ℝ) 0) h
        simp at this
    have hfin : Module.finrank ℝ (Fin (m + 2) → ℝ) = m + 2 := by simp
    rw [hfin] at hrn
    change Module.finrank ℝ (LinearMap.range (gram (m + 2) c).mulVecLin) ≤ m + 1
    omega
  · have h1 := Matrix.rank_submatrix_le (gram (m + 2) c) (Fin.castLE (by omega : m + 1 ≤ m + 2))
      (Fin.castLE (by omega : m + 1 ≤ m + 2))
    rw [principal_gram] at h1
    have h2 : (gram (m + 1) c).rank = m + 1 := by
      refine rank_gram_of_det_ne (n := m) (c := c) ?_ ?_
      · rw [hc]; intro h; field_simp at h; linarith
      · have : 1 + (m : ℝ) * c = 1 / ((m : ℝ) + 1) := by rw [hc]; field_simp; ring
        rw [this]; positivity
    omega

end CubicRhombus
