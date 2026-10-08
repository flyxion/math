import Mathlib

/-!
# A linear-plus-translation map that sends the vertices of the cube to vertices of the cube sends
each coordinate direction to a signed coordinate direction.
-/

namespace CubicRhombus

open Finset

variable {d : ℕ}

theorem cube_affine (M : (Fin d → ℝ) →ₗ[ℝ] (Fin d → ℝ)) (w : Fin d → ℝ)
    (hinj : Function.Injective M)
    (h : ∀ z : Fin d → ℝ, (∀ k, z k = 0 ∨ z k = 1) → ∀ k, (M z + w) k = 0 ∨ (M z + w) k = 1) :
    ∀ i, ∃ j, ∃ σ : ℝ, (σ = 1 ∨ σ = -1) ∧ M (Pi.single i 1) = σ • Pi.single j 1 := by
  classical
  set a : Fin d → Fin d → ℝ := fun k i => M (Pi.single i 1) k with ha
  have hw : ∀ k, w k = 0 ∨ w k = 1 := by
    intro k
    have := h 0 (fun _ => Or.inl rfl) k
    simpa using this
  have h1 : ∀ k i, w k + a k i = 0 ∨ w k + a k i = 1 := by
    intro k i
    have := h (Pi.single i 1) (fun l => by
      by_cases hl : l = i
      · subst hl; simp
      · simp [hl]) k
    simpa [ha, add_comm] using this
  have h2 : ∀ k i i', i ≠ i' → w k + a k i + a k i' = 0 ∨ w k + a k i + a k i' = 1 := by
    intro k i i' hne
    have := h (Pi.single i 1 + Pi.single i' 1) (fun l => by
      by_cases hl : l = i
      · subst hl; simp [Pi.single_apply, hne]
      · by_cases hl' : l = i'
        · subst hl'; simp [Pi.single_apply, hl]
        · simp [Pi.single_apply, hl, hl']) k
    simp only [map_add, Pi.add_apply] at this
    simpa [ha, add_comm, add_left_comm, add_assoc] using this
  have hA : ∀ k i i', i ≠ i' → a k i = 0 ∨ a k i' = 0 := by
    intro k i i' hne
    by_contra hcon
    push_neg at hcon
    obtain ⟨n1, n2⟩ := hcon
    rcases hw k with hk | hk <;> rcases h1 k i with p | p <;> rcases h1 k i' with q | q <;>
      rcases h2 k i i' hne with r | r <;>
      first
        | exact absurd (by linarith) n1
        | exact absurd (by linarith) n2
        | (exfalso; linarith)
  have hval : ∀ k i, a k i = 0 ∨ a k i = 1 ∨ a k i = -1 := by
    intro k i
    rcases hw k with hk | hk <;> rcases h1 k i with p | p
    all_goals first | (left; linarith) | (right; left; linarith) | (right; right; linarith)
  have hcol : ∀ i, ∃ k, a k i ≠ 0 := by
    intro i
    by_contra hcon
    push_neg at hcon
    have : M (Pi.single i 1) = M 0 := by
      ext k; simpa [ha] using hcon k
    have := hinj this
    have := congrFun this i
    simp at this
  set R : Fin d → Finset (Fin d) := fun i => univ.filter fun k => a k i ≠ 0 with hR
  have hdisj : ((univ : Finset (Fin d)) : Set (Fin d)).PairwiseDisjoint R := by
    intro i _ i' _ hne
    rw [Function.onFun, Finset.disjoint_left]
    intro k hk hk'
    simp only [hR, mem_filter, mem_univ, true_and] at hk hk'
    rcases hA k i i' hne with h | h
    · exact hk h
    · exact hk' h
  have hsum : ∑ i, (R i).card ≤ d := by
    have := Finset.card_biUnion (s := univ) (t := R) (fun i hi i' hi' hne => hdisj hi hi' hne)
    rw [← this]
    calc _ ≤ (univ : Finset (Fin d)).card := Finset.card_le_univ _
      _ = d := by simp
  have hone : ∀ i, (R i).card = 1 := by
    intro i0
    by_contra hne
    have hge : ∀ i, 1 ≤ (R i).card := fun i => by
      obtain ⟨k, hk⟩ := hcol i
      exact Finset.card_pos.mpr ⟨k, by simp [hR, hk]⟩
    have hgt : 1 < (R i0).card := lt_of_le_of_ne (hge i0) (Ne.symm hne)
    have : ∑ _i : Fin d, 1 < ∑ i, (R i).card :=
      Finset.sum_lt_sum (fun i _ => hge i) ⟨i0, mem_univ _, hgt⟩
    simp at this
    omega
  intro i
  obtain ⟨j, hj⟩ := Finset.card_eq_one.mp (hone i)
  have hjmem : j ∈ R i := by rw [hj]; simp
  have hjne : a j i ≠ 0 := by simpa [hR] using hjmem
  have hzero : ∀ k, k ≠ j → a k i = 0 := by
    intro k hk
    by_contra hnz
    have : k ∈ R i := by simp [hR, hnz]
    rw [hj] at this
    simp at this
    exact hk this
  refine ⟨j, a j i, ?_, ?_⟩
  · rcases hval j i with h | h | h
    · exact absurd h hjne
    · left; exact h
    · right; exact h
  · ext k
    by_cases hk : k = j
    · subst hk; simp [ha]
    · have := hzero k hk
      simp only [ha] at this
      simp [Pi.single_apply, hk, this]

end CubicRhombus
