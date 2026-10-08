import Mathlib
import CubicRhombus.Gram
import CubicRhombus.Theorems

/-!
# Euclidean geometry of the cubic rhombus

* `volume_sq_eq_det`: the Lebesgue volume of the parallelotope spanned by `d` vectors of
  `EuclideanSpace ℝ (Fin d)` squares to the determinant of their Gram matrix.
* `exists_system`: for `-1/n < c < 1` there are vectors with Gram matrix `gram (n+1) c`.
* `volume_rhombus`: hence the rhombus has squared volume `vol2 n c`.
-/

open MeasureTheory
open scoped MatrixOrder Matrix

namespace CubicRhombus

/-- The inner product Gram matrix of a family of vectors. -/
noncomputable def ipGram {d : ℕ} (e : Fin d → EuclideanSpace ℝ (Fin d)) : Matrix (Fin d) (Fin d) ℝ :=
  Matrix.of fun i j => inner ℝ (e i) (e j)

theorem volume_sq_eq_det {d : ℕ} (e : Fin d → EuclideanSpace ℝ (Fin d)) :
    ((volume (parallelepiped e)).toReal) ^ 2 = (ipGram e).det := by
  have hb : volume = (EuclideanSpace.basisFun (Fin d) ℝ).toBasis.addHaar :=
    ((EuclideanSpace.basisFun (Fin d) ℝ).addHaar_eq_volume).symm
  rw [hb, Measure.addHaar_parallelepiped, ENNReal.toReal_ofReal (abs_nonneg _), sq_abs,
    Module.Basis.det_apply]
  have h := Matrix.gram_eq_conjTranspose_mul (𝕜 := ℝ) (EuclideanSpace.basisFun (Fin d) ℝ) e
  have h2 : ipGram e = Matrix.gram ℝ e := rfl
  rw [h2, h]
  simp [Matrix.det_mul, Matrix.det_conjTranspose, sq]
  rfl

/-- The Gram matrix is positive semidefinite on `[-1/n, 1]`-interior, as a Mathlib `PosSemidef`. -/
theorem posSemidef_gram {n : ℕ} {c : ℝ} (hlo : -1 < n * c) (hhi : c < 1) :
    (gram (n + 1) c).PosSemidef := by
  refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg ?_ fun x => ?_
  · ext i j
    by_cases h : i = j
    · subst h; simp [gram]
    · simp [gram, h, Ne.symm h]
  · by_cases hx : (x : Fin (n + 1) → ℝ) = 0
    · simp [hx]
    · simpa using (quadForm_gram_pos hlo hhi hx).le

/-- **T1, existence.**  For `-1/n < c < 1` there are `n + 1` vectors of `ℝ^(n+1)` with Gram
matrix `gram (n+1) c`, namely unit vectors with all pairwise inner products equal to `c`. -/
theorem exists_system {n : ℕ} {c : ℝ} (hlo : -1 < n * c) (hhi : c < 1) :
    ∃ e : Fin (n + 1) → EuclideanSpace ℝ (Fin (n + 1)), ipGram e = gram (n + 1) c := by
  have hP := posSemidef_gram hlo hhi
  set S := CFC.sqrt (gram (n + 1) c) with hS
  have hSpsd : S.PosSemidef := (Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg (gram (n + 1) c)))
  have hSS : S * S = gram (n + 1) c := CFC.sqrt_mul_sqrt_self _ hP.nonneg
  refine ⟨fun i => WithLp.toLp 2 (S i), ?_⟩
  ext i j
  have hh : Sᴴ = S := hSpsd.isHermitian
  have : (S * S) i j = ∑ k, S i k * S j k := by
    rw [Matrix.mul_apply]
    refine Finset.sum_congr rfl fun k _ => ?_
    have := congrFun (congrFun hh k) j
    simp only [Matrix.conjTranspose_apply, star_trivial] at this
    rw [← this]
  rw [← hSS, this]
  simp [ipGram, PiLp.inner_apply, mul_comm]

/-- **The volume of the cubic rhombus.**  Any `n + 1` vectors of `ℝ^(n+1)` with pairwise inner
products `c` and unit length span a parallelotope of Lebesgue volume `V` with `V^2 = vol2 n c`. -/
theorem volume_sq_rhombus {n : ℕ} {c : ℝ} (e : Fin (n + 1) → EuclideanSpace ℝ (Fin (n + 1)))
    (he : ipGram e = gram (n + 1) c) :
    ((MeasureTheory.volume (parallelepiped e)).toReal) ^ 2 = vol2 n c := by
  rw [volume_sq_eq_det, he, det_gram]

/-- The sharp inequality in Euclidean form (T2): the rhombus has volume at most `1`. -/
theorem volume_rhombus_le_one {n : ℕ} {c : ℝ} (hlo : -1 < n * c) (hhi : c < 1)
    (e : Fin (n + 1) → EuclideanSpace ℝ (Fin (n + 1))) (he : ipGram e = gram (n + 1) c) :
    (MeasureTheory.volume (parallelepiped e)).toReal ≤ 1 := by
  have h := volume_sq_rhombus e he
  have h1 := vol2_le_one hlo hhi
  nlinarith [ENNReal.toReal_nonneg (a := MeasureTheory.volume (parallelepiped e))]

end CubicRhombus
