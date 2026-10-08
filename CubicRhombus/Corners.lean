import Mathlib
import CubicRhombus.Gram
import CubicRhombus.Plane

/-!
# S05 / S13: boundary rigidity at the level of vertex configurations

At the vertex of the parallelotope `P(e)` indexed by `σ : Fin d → Bool` the edges leave along
`±e i` (sign `-1` when `σ i = true`).  The Gram matrix of that corner is `D_σ G D_σ`.  The set of
corner Gram matrices is the local geometry of the boundary.  We prove:

* for `d ≥ 3` the set of corner Gram matrices determines `c`;
* for `d = 2` it does not: `R_2(c)` and `R_2(-c)` have the same set of corners.

What is *not* proved here: that an isometry of the whole boundary carries corners to corners
(which is a statement about isometries of polytopes, not about Gram matrices).
-/

namespace CubicRhombus

/-- The sign attached to a bit. -/
def sgn (b : Bool) : ℝ := if b then -1 else 1

/-- Gram matrix of the corner of the rhombus `R_d(c)` at vertex `σ`. -/
noncomputable def corner (d : ℕ) (c : ℝ) (σ : Fin d → Bool) : Matrix (Fin d) (Fin d) ℝ :=
  Matrix.of fun i j => sgn (σ i) * sgn (σ j) * gram d c i j

/-- The set of all corner Gram matrices. -/
def cornerSet (d : ℕ) (c : ℝ) : Set (Matrix (Fin d) (Fin d) ℝ) := Set.range (corner d c)

lemma sgn_sq (b : Bool) : sgn b * sgn b = 1 := by cases b <;> simp [sgn]

/-- **S05 / S13 (d ≥ 3).**  The set of corner Gram matrices determines the parameter. -/
theorem cornerSet_eq_iff {d : ℕ} {c s : ℝ} :
    cornerSet (d + 3) c = cornerSet (d + 3) s ↔ c = s := by
  constructor
  · intro h
    have hmem : corner (d + 3) c (fun _ => false) ∈ cornerSet (d + 3) s := by
      rw [← h]; exact ⟨_, rfl⟩
    obtain ⟨σ, hσ⟩ := hmem
    have n01 : (0 : Fin (d + 3)) ≠ 1 := by
      intro h; have := congrArg Fin.val h; rw [Fin.val_zero, Fin.val_one] at this; omega
    have n02 : (0 : Fin (d + 3)) ≠ 2 := by
      intro h; have := congrArg Fin.val h; rw [Fin.val_zero, Fin.val_two] at this; omega
    have n12 : (1 : Fin (d + 3)) ≠ 2 := by
      intro h; have := congrArg Fin.val h; rw [Fin.val_one, Fin.val_two] at this; omega
    have e01 := congrFun (congrFun hσ 0) 1
    have e02 := congrFun (congrFun hσ 0) 2
    have e12 := congrFun (congrFun hσ 1) 2
    simp only [corner, Matrix.of_apply, gram, n01, n02, n12, if_false, sgn, Bool.false_eq_true,
      mul_one, one_mul] at e01 e02 e12
    cases h0 : σ 0 <;> cases h1 : σ 1 <;> cases h2 : σ 2 <;>
      simp [h0, h1, h2, sgn] at e01 e02 e12 <;> linarith
  · rintro rfl; rfl

private lemma corner2_subset (c : ℝ) : cornerSet 2 c ⊆ cornerSet 2 (-c) := by
  rintro _ ⟨σ, rfl⟩
  refine ⟨fun i => if i = 1 then !σ i else σ i, ?_⟩
  ext i j
  have hi : ∀ k : Fin 2, k = 0 ∨ k = 1 := by decide
  rcases hi i with rfl | rfl <;> rcases hi j with rfl | rfl <;>
    cases h0 : σ 0 <;> cases h1 : σ 1 <;> simp [corner, gram, sgn, h0, h1]

/-- **S08 contrast (d = 2).**  `R_2(c)` and `R_2(-c)` have the same corners, so corners cannot
distinguish `c` from `-c`. -/
theorem cornerSet_two_neg (c : ℝ) : cornerSet 2 c = cornerSet 2 (-c) := by
  refine Set.Subset.antisymm (corner2_subset c) ?_
  have := corner2_subset (-c)
  rwa [neg_neg] at this

theorem cornerSet_two_not_determined : ∃ c s : ℝ, c ≠ s ∧ cornerSet 2 c = cornerSet 2 s :=
  ⟨1 / 2, -(1 / 2), by norm_num, cornerSet_two_neg _⟩

end CubicRhombus
