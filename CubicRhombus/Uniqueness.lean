import Mathlib
import CubicRhombus.Gram
import CubicRhombus.Geometry
import CubicRhombus.Rank

/-!
# S01, uniqueness: a family of vectors is determined by its Gram matrix up to an orthogonal map
-/

namespace CubicRhombus

open Finset
open scoped Matrix

variable {d : ℕ}

private lemma norm_sq_comb (e : Fin d → EuclideanSpace ℝ (Fin d)) (a : Fin d → ℝ) :
    ‖∑ i, a i • e i‖ ^ 2 = ∑ i, ∑ j, a i * a j * ipGram e i j := by
  rw [← real_inner_self_eq_norm_sq, sum_inner]
  refine sum_congr rfl fun i _ => ?_
  rw [inner_sum]
  refine sum_congr rfl fun j _ => ?_
  rw [real_inner_smul_left, real_inner_smul_right]
  simp [ipGram, mul_assoc]

/-- **S01, uniqueness.**  Two families with the same Gram matrix differ by a linear isometry of the
ambient Euclidean space. -/
theorem exists_isometry_of_ipGram_eq (e f : Fin d → EuclideanSpace ℝ (Fin d))
    (h : ipGram e = ipGram f) :
    ∃ T : EuclideanSpace ℝ (Fin d) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin d), ∀ i, T (e i) = f i := by
  set Φe : (Fin d → ℝ) →ₗ[ℝ] EuclideanSpace ℝ (Fin d) := Fintype.linearCombination ℝ e with hΦe
  set Φf : (Fin d → ℝ) →ₗ[ℝ] EuclideanSpace ℝ (Fin d) := Fintype.linearCombination ℝ f with hΦf
  have hne : ∀ a, ‖Φe a‖ = ‖Φf a‖ := by
    intro a
    have h1 : Φe a = ∑ i, a i • e i := by simp [hΦe, Fintype.linearCombination_apply]
    have h2 : Φf a = ∑ i, a i • f i := by simp [hΦf, Fintype.linearCombination_apply]
    have := norm_sq_comb e a
    have h3 := norm_sq_comb f a
    rw [h] at this
    rw [h1, h2]
    have : ‖∑ i, a i • e i‖ ^ 2 = ‖∑ i, a i • f i‖ ^ 2 := by rw [this, h3]
    exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp this
  -- right inverse onto the range of Φe
  obtain ⟨R, hR⟩ := Φe.rangeRestrict.exists_rightInverse_of_surjective Φe.range_rangeRestrict
  let L0 : LinearMap.range Φe →ₗ[ℝ] EuclideanSpace ℝ (Fin d) := Φf ∘ₗ R
  have hRe : ∀ x : LinearMap.range Φe, Φe (R x) = x := by
    intro x
    have := congrArg (fun g => (g x : EuclideanSpace ℝ (Fin d))) hR
    simpa using this
  have hL0 : ∀ x, ‖L0 x‖ = ‖x‖ := by
    intro x
    show ‖Φf (R x)‖ = ‖x‖
    rw [← hne, hRe]; rfl
  let L : LinearMap.range Φe →ₗᵢ[ℝ] EuclideanSpace ℝ (Fin d) := ⟨L0, hL0⟩
  have hL : ∀ a : Fin d → ℝ, L ⟨Φe a, a, rfl⟩ = Φf a := by
    intro a
    have hker : ∀ b, Φe b = 0 → Φf b = 0 := by
      intro b hb
      have := hne b; rw [hb, norm_zero] at this; exact norm_eq_zero.mp this.symm
    have hdiff : Φe (R ⟨Φe a, a, rfl⟩ - a) = 0 := by
      rw [map_sub, hRe]; simp
    have := hker _ hdiff
    rw [map_sub, sub_eq_zero] at this
    show Φf (R ⟨Φe a, a, rfl⟩) = Φf a
    exact this
  let T0 := L.extend
  let T := T0.toLinearIsometryEquiv rfl
  refine ⟨T, fun i => ?_⟩
  have hei : e i = Φe (Pi.single i 1) := by simp [hΦe, Fintype.linearCombination_apply]
  have hfi : f i = Φf (Pi.single i 1) := by simp [hΦf, Fintype.linearCombination_apply]
  show T0 (e i) = f i
  have hmem : e i ∈ LinearMap.range Φe := ⟨Pi.single i 1, hei.symm⟩
  have := L.extend_apply ⟨e i, hmem⟩
  rw [show T0 (e i) = T0 ((⟨e i, hmem⟩ : LinearMap.range Φe) : EuclideanSpace ℝ (Fin d)) from rfl,
    this]
  have := hL (Pi.single i 1)
  rw [hfi]
  convert this using 2
  exact Subtype.ext hei

/-- **The rank of a family of vectors is the rank of its Gram matrix.**  This closes the gap in
the S04 statement: `rank_interior`, `rank_upper`, `rank_lower` are statements about the dimension
of the span of the edge vectors. -/
theorem finrank_span_eq_rank_ipGram (e : Fin d → EuclideanSpace ℝ (Fin d)) :
    Module.finrank ℝ (Submodule.span ℝ (Set.range e)) = (ipGram e).rank := by
  set b := EuclideanSpace.basisFun (Fin d) ℝ
  set m : Matrix (Fin d) (Fin d) ℝ := Matrix.of fun i j => b.repr (e j) i with hm
  have h1 : ipGram e = mᴴ * m := Matrix.gram_eq_conjTranspose_mul b e
  rw [h1, Matrix.rank_conjTranspose_mul_self, Matrix.rank_eq_finrank_span_cols]
  let Ψ : EuclideanSpace ℝ (Fin d) ≃ₗ[ℝ] (Fin d → ℝ) :=
    b.repr.toLinearEquiv.trans (WithLp.linearEquiv 2 ℝ (Fin d → ℝ))
  have hcols : Set.range m.col = (Ψ.toLinearMap : EuclideanSpace ℝ (Fin d) →ₗ[ℝ] (Fin d → ℝ))
        '' Set.range e := by
    ext x; constructor
    · rintro ⟨j, rfl⟩; exact ⟨e j, ⟨j, rfl⟩, by ext i; simp [hm, Ψ]⟩
    · rintro ⟨y, ⟨j, rfl⟩, rfl⟩; exact ⟨j, by ext i; simp [hm, Ψ]⟩
  rw [hcols, ← Submodule.map_span]
  exact (LinearEquiv.finrank_map_eq Ψ _).symm

/-- **S01, uniqueness for the rhombus.**  Any two systems with parameter `c` are congruent. -/
theorem rhombus_unique {n : ℕ} {c : ℝ} (e f : Fin (n + 1) → EuclideanSpace ℝ (Fin (n + 1)))
    (he : ipGram e = gram (n + 1) c) (hf : ipGram f = gram (n + 1) c) :
    ∃ T : EuclideanSpace ℝ (Fin (n + 1)) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin (n + 1)), ∀ i, T (e i) = f i :=
  exists_isometry_of_ipGram_eq e f (he.trans hf.symm)

/-- **S04 for vector families, interior.** -/
theorem span_dim_interior {n : ℕ} {c : ℝ} (hlo : -1 < n * c) (hhi : c < 1)
    (e : Fin (n + 1) → EuclideanSpace ℝ (Fin (n + 1))) (he : ipGram e = gram (n + 1) c) :
    Module.finrank ℝ (Submodule.span ℝ (Set.range e)) = n + 1 := by
  rw [finrank_span_eq_rank_ipGram, he, rank_interior hlo hhi]

/-- **S04 for vector families, upper endpoint.** -/
theorem span_dim_upper {n : ℕ} (e : Fin (n + 1) → EuclideanSpace ℝ (Fin (n + 1)))
    (he : ipGram e = gram (n + 1) 1) :
    Module.finrank ℝ (Submodule.span ℝ (Set.range e)) = 1 := by
  rw [finrank_span_eq_rank_ipGram, he, rank_upper]

/-- **S04 for vector families, lower endpoint.** -/
theorem span_dim_lower {m : ℕ} (e : Fin (m + 2) → EuclideanSpace ℝ (Fin (m + 2)))
    (he : ipGram e = gram (m + 2) (-(1 : ℝ) / (m + 1))) :
    Module.finrank ℝ (Submodule.span ℝ (Set.range e)) = m + 1 := by
  rw [finrank_span_eq_rank_ipGram, he, rank_lower]

end CubicRhombus
