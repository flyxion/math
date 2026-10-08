import Mathlib
import CubicRhombus.Gram
import CubicRhombus.Geometry

/-!
# S08 / T8, dimension two: `R_2(c)` and `R_2(-c)` are congruent

Flipping one edge vector changes the sign of the inner product, and the parallelogram is moved
onto itself's translate.  In dimension `d ≥ 3` flipping one vector produces mixed signs, so the
parameter `c` is recoverable from the shape (the contrast with S07).
-/

namespace CubicRhombus


/-- Flip the second edge vector of a planar system. -/
def flip2 {E : Type*} [Neg E] (e : Fin 2 → E) : Fin 2 → E := ![e 0, -e 1]

/-- **Gram matrices.**  Flipping the second edge sends the inner product `c` to `-c`. -/
theorem ipGram_flip2 {c : ℝ} (e : Fin 2 → EuclideanSpace ℝ (Fin 2))
    (he : ipGram e = gram 2 c) : ipGram (flip2 e) = gram 2 (-c) := by
  have h00 : inner ℝ (e 0) (e 0) = 1 := by
    have := congrFun (congrFun he 0) 0; simpa [ipGram, gram] using this
  have h11 : inner ℝ (e 1) (e 1) = 1 := by
    have := congrFun (congrFun he 1) 1; simpa [ipGram, gram] using this
  have h01 : inner ℝ (e 0) (e 1) = c := by
    have := congrFun (congrFun he 0) 1; simpa [ipGram, gram] using this
  have h10 : inner ℝ (e 1) (e 0) = c := by
    have := congrFun (congrFun he 1) 0; simpa [ipGram, gram] using this
  have n0 : ‖e 0‖ ^ 2 = 1 := by rw [← real_inner_self_eq_norm_sq]; exact h00
  have n1 : ‖e 1‖ ^ 2 = 1 := by rw [← real_inner_self_eq_norm_sq]; exact h11
  have n0' : ‖e 0‖ = 1 := by nlinarith [norm_nonneg (e 0)]
  have n1' : ‖e 1‖ = 1 := by nlinarith [norm_nonneg (e 1)]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [ipGram, gram, flip2, h00, h11, h01, h10, n0', n1']

/-- **Congruence.**  The parallelograms spanned by `e` and by the flipped system are translates of
one another, so they are congruent. -/
theorem parallelepiped_flip2 {E : Type*} [AddCommGroup E] [Module ℝ E] (e : Fin 2 → E) :
    (fun x => x + e 1) '' parallelepiped (flip2 e) = parallelepiped e := by
  ext x
  simp only [Set.mem_image, mem_parallelepiped_iff, Fin.sum_univ_two, flip2]
  constructor
  · rintro ⟨y, ⟨t, ht, rfl⟩, rfl⟩
    refine ⟨![t 0, 1 - t 1], ?_, ?_⟩
    · have a0 : 0 ≤ t 0 := ht.1 0
      have a1 : 0 ≤ t 1 := ht.1 1
      have b0 : t 0 ≤ 1 := ht.2 0
      have b1 : t 1 ≤ 1 := ht.2 1
      refine ⟨fun i => ?_, fun i => ?_⟩ <;> fin_cases i <;> simp <;> linarith
    · simp [sub_smul]; abel
  · rintro ⟨s, hs, rfl⟩
    refine ⟨_, ⟨![s 0, 1 - s 1], ?_, rfl⟩, ?_⟩
    · have a0 : 0 ≤ s 0 := hs.1 0
      have a1 : 0 ≤ s 1 := hs.1 1
      have b0 : s 0 ≤ 1 := hs.2 0
      have b1 : s 1 ≤ 1 := hs.2 1
      refine ⟨fun i => ?_, fun i => ?_⟩ <;> fin_cases i <;> simp <;> linarith
    · simp [sub_smul]; abel

/-- Hence the two rhombi have the same volume, as `vol2 1 c = vol2 1 (-c)` would suggest... -/
theorem vol2_two_symm (c : ℝ) : vol2 1 c = 1 - c ^ 2 ∧ vol2 1 (-c) = 1 - c ^ 2 := by
  constructor <;> simp [vol2] <;> ring

/-- The Gram matrix after flipping edge vector `k`. -/
def flipGram (d : ℕ) (k : Fin d) (c : ℝ) : Matrix (Fin d) (Fin d) ℝ :=
  Matrix.of fun i j => (if i = k then -1 else 1) * (if j = k then -1 else 1) * gram d c i j

/-- In dimension two the flip lands back in the family, with parameter `-c`. -/
theorem flipGram_two (c : ℝ) : flipGram 2 1 c = gram 2 (-c) := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [flipGram, gram]

/-- **The contrast with S07.**  In dimension `d ≥ 3`, flipping one edge vector leaves the family
unless `c = 0`: the flipped Gram matrix has entries `c` and `-c` off the diagonal. -/
theorem flipGram_not_member {d : ℕ} {c : ℝ} (hc : c ≠ 0) (s : ℝ) :
    flipGram (d + 3) 2 c ≠ gram (d + 3) s := by
  intro h
  have h1 := congrFun (congrFun h 0) 1
  have h2 := congrFun (congrFun h 0) 2
  have n02 : (0 : Fin (d + 3)) ≠ 2 := by
    intro h; have := congrArg Fin.val h; rw [Fin.val_zero, Fin.val_two] at this; omega
  have n12 : (1 : Fin (d + 3)) ≠ 2 := by
    intro h; have := congrArg Fin.val h; rw [Fin.val_one, Fin.val_two] at this; omega
  have n01 : (0 : Fin (d + 3)) ≠ 1 := by
    intro h; have := congrArg Fin.val h; rw [Fin.val_zero, Fin.val_one] at this; omega
  simp [flipGram, gram, n02, n12, n01] at h1 h2
  apply hc
  linarith

end CubicRhombus
