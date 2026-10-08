import Mathlib
import CubicRhombus.Gram
import CubicRhombus.Geometry
import CubicRhombus.CubeAut
import CubicRhombus.Corners
import CubicRhombus.Plane

/-!
# S05 / S13: congruent rhombi have the same parameter (`d ≥ 3`)

If an isometry of `ℝ^d` maps the parallelotope `P(e)` onto `P(f)` then it maps vertices to
vertices, hence edge directions to signed edge directions, hence `⟨e i, e j⟩ = ±⟨f j', f j''⟩`.
For rhombi with `d ≥ 3` this forces the parameters to be equal.
-/

open Set

namespace CubicRhombus

variable {d : ℕ}

abbrev V (d : ℕ) := EuclideanSpace ℝ (Fin d)

/-- Vertex coordinates of the unit cube. -/
def cubeVerts (d : ℕ) : Set (Fin d → ℝ) := {z | ∀ k, z k = 0 ∨ z k = 1}

lemma affine_image_extremePoints (A : V d ≃ᵃ[ℝ] V d) (S : Set (V d)) :
    A '' extremePoints ℝ S = extremePoints ℝ (A '' S) := by
  have hseg : ∀ x y, A '' openSegment ℝ x y = openSegment ℝ (A x) (A y) :=
    fun x y => by simpa using image_openSegment ℝ A.toAffineMap x y
  ext b
  obtain ⟨a, rfl⟩ := A.surjective b
  constructor
  · rintro ⟨x, hx, hxa⟩
    have hxa' : x = a := A.injective hxa
    subst hxa'
    rw [mem_extremePoints] at hx ⊢
    refine ⟨⟨x, hx.1, rfl⟩, ?_⟩
    rintro _ ⟨y, hy, rfl⟩ _ ⟨z, hz, rfl⟩ hseg'
    rw [← hseg] at hseg'
    obtain ⟨w, hw, hwx⟩ := hseg'
    have := A.injective hwx
    subst this
    obtain ⟨h1, h2⟩ := hx.2 y hy z hz hw
    exact ⟨by rw [h1], by rw [h2]⟩
  · intro h
    rw [mem_extremePoints] at h
    refine ⟨a, ?_, rfl⟩
    rw [mem_extremePoints]
    obtain ⟨⟨a', ha', haa⟩, h2⟩ := h
    have : a' = a := A.injective haa
    subst this
    refine ⟨ha', fun y hy z hz hyz => ?_⟩
    have := h2 (A y) ⟨y, hy, rfl⟩ (A z) ⟨z, hz, rfl⟩ (by rw [← hseg]; exact ⟨a', hyz, rfl⟩)
    exact ⟨A.injective this.1, A.injective this.2⟩

/-- The linear equivalence `ℝ^d ≃ V` determined by a basis family. -/
noncomputable def basisOf (e : Fin d → V d) (h : LinearIndependent ℝ e) : Module.Basis (Fin d) ℝ (V d) :=
  Module.Basis.mk h (le_of_eq (h.span_eq_top_of_card_eq_finrank'
    (by rw [Fintype.card_fin, finrank_euclideanSpace, Fintype.card_fin])).symm)

/-- The linear equivalence `ℝ^d ≃ V` determined by a basis family. -/
noncomputable def basisEquiv (e : Fin d → V d) (h : LinearIndependent ℝ e) :
    (Fin d → ℝ) ≃ₗ[ℝ] V d :=
  (basisOf e h).equivFun.symm

lemma basisEquiv_apply (e : Fin d → V d) (h : LinearIndependent ℝ e) (z : Fin d → ℝ) :
    basisEquiv e h z = ∑ i, z i • e i := by
  simp [basisEquiv, basisOf, Module.Basis.equivFun_symm_apply]

lemma basisEquiv_single (e : Fin d → V d) (h : LinearIndependent ℝ e) (i : Fin d) :
    basisEquiv e h (Pi.single i 1) = e i := by
  rw [basisEquiv_apply]; simp [Pi.single_apply]

lemma parallelepiped_eq_image (e : Fin d → V d) (h : LinearIndependent ℝ e) :
    parallelepiped e = basisEquiv e h '' Icc 0 1 := by
  ext x
  rw [mem_parallelepiped_iff]
  constructor
  · rintro ⟨t, ht, rfl⟩; exact ⟨t, ht, (basisEquiv_apply e h t)⟩
  · rintro ⟨t, ht, rfl⟩; exact ⟨t, ht, (basisEquiv_apply e h t)⟩

/-- The extreme points of a parallelotope are its vertices. -/
theorem extremePoints_parallelepiped (e : Fin d → V d) (h : LinearIndependent ℝ e) :
    extremePoints ℝ (parallelepiped e) = basisEquiv e h '' cubeVerts d := by
  rw [parallelepiped_eq_image e h, ← image_extremePoints (basisEquiv e h)]
  congr 1
  rw [← Set.pi_univ_Icc]
  rw [extremePoints_pi]
  ext z
  simp [cubeVerts, Set.mem_pi]

/-- **Edges go to signed edges.**  An isometry carrying `P(e)` onto `P(f)` maps every edge vector
`e i` (under its linear part) to `±f j`. -/
theorem edge_to_signed_edge (e f : Fin d → V d) (he : LinearIndependent ℝ e)
    (hf : LinearIndependent ℝ f) (T : V d ≃ᵃⁱ[ℝ] V d) (hT : T '' parallelepiped e = parallelepiped f)
    (i : Fin d) :
    ∃ j, ∃ σ : ℝ, (σ = 1 ∨ σ = -1) ∧ T.linearIsometryEquiv (e i) = σ • f j := by
  set L := T.linearIsometryEquiv with hL
  set Φe := basisEquiv e he
  set Φf := basisEquiv f hf
  have hTx : ∀ x, T x = L x + T 0 := by
    intro x
    have := T.map_vadd (0 : V d) x
    simpa [hL, add_comm] using this
  -- vertices go to vertices
  have hvert : ∀ z ∈ cubeVerts d, Φf.symm (T (Φe z)) ∈ cubeVerts d := by
    intro z hz
    have h1 : Φe z ∈ extremePoints ℝ (parallelepiped e) := by
      rw [extremePoints_parallelepiped e he]; exact ⟨z, hz, rfl⟩
    have h2 : T (Φe z) ∈ extremePoints ℝ (parallelepiped f) := by
      have key := affine_image_extremePoints T.toAffineEquiv (parallelepiped e)
      have hm : T.toAffineEquiv (Φe z) ∈ T.toAffineEquiv '' extremePoints ℝ (parallelepiped e) :=
        ⟨Φe z, h1, rfl⟩
      rw [key] at hm
      rw [← hT]
      exact hm
    rw [extremePoints_parallelepiped f hf] at h2
    obtain ⟨z', hz', hzz⟩ := h2
    rw [← hzz, LinearEquiv.symm_apply_apply]; exact hz'
  let M : (Fin d → ℝ) →ₗ[ℝ] (Fin d → ℝ) :=
    Φf.symm.toLinearMap ∘ₗ L.toLinearEquiv.toLinearMap ∘ₗ Φe.toLinearMap
  have hMapp : ∀ z, Φf.symm (T (Φe z)) = M z + Φf.symm (T 0) := by
    intro z
    rw [hTx (Φe z), map_add]; rfl
  have hinj : Function.Injective M := by
    intro x y hxy
    have : Φf.symm.toLinearMap (L.toLinearEquiv.toLinearMap (Φe.toLinearMap x)) =
        Φf.symm.toLinearMap (L.toLinearEquiv.toLinearMap (Φe.toLinearMap y)) := hxy
    simpa using this
  have hcube := cube_affine M (Φf.symm (T 0)) hinj (by
    intro z hz k
    have := hvert z hz k
    rwa [hMapp] at this)
  obtain ⟨j, σ, hσ, hM⟩ := hcube i
  refine ⟨j, σ, hσ, ?_⟩
  have h1 : L (e i) = Φf (M (Pi.single i 1)) := by
    have : M (Pi.single i 1) = Φf.symm (L (Φe (Pi.single i 1))) := rfl
    rw [this, LinearEquiv.apply_symm_apply, basisEquiv_single]
  rw [h1, hM, map_smul, basisEquiv_single]

lemma linIndep_of_ipGram {n : ℕ} {c : ℝ} (hlo : -1 < n * c) (hhi : c < 1)
    (e : Fin (n + 1) → V (n + 1)) (he : ipGram e = gram (n + 1) c) : LinearIndependent ℝ e := by
  rw [← Matrix.det_gram_ne_zero_iff_linearIndependent (𝕜 := ℝ)]
  have : Matrix.gram ℝ e = ipGram e := rfl
  rw [this, he, det_gram]
  have ha : 0 < 1 - c := by linarith
  have hb : 0 < 1 + n * c := by linarith
  exact (mul_pos (pow_pos ha n) hb).ne'

/-- **S05 / S13, geometric form.**  If an isometry of `ℝ^(m+3)` carries the rhombus `P(e)` with
parameter `c` onto the rhombus `P(f)` with parameter `s`, then `c = s`. -/
theorem congruent_rhombi_param_eq {m : ℕ} {c s : ℝ}
    (hlo : -1 < ((m + 2 : ℕ) : ℝ) * c) (hhi : c < 1)
    (hlo' : -1 < ((m + 2 : ℕ) : ℝ) * s) (hhi' : s < 1)
    (e f : Fin (m + 3) → V (m + 3))
    (he : ipGram e = gram (m + 3) c) (hf : ipGram f = gram (m + 3) s)
    (T : V (m + 3) ≃ᵃⁱ[ℝ] V (m + 3)) (hT : T '' parallelepiped e = parallelepiped f) :
    c = s := by
  have hLe := linIndep_of_ipGram hlo hhi e he
  have hLf := linIndep_of_ipGram hlo' hhi' f hf
  set L := T.linearIsometryEquiv with hL
  have hcne : ∀ a b : Fin (m + 3), a ≠ b → inner ℝ (e a) (e b) = c := by
    intro a b hab
    have := congrFun (congrFun he a) b
    simpa [ipGram, gram, hab] using this
  have key : ∀ a b : Fin (m + 3), a ≠ b → ∀ ja jb : Fin (m + 3), ∀ σa σb : ℝ,
      (σa = 1 ∨ σa = -1) → (σb = 1 ∨ σb = -1) → L (e a) = σa • f ja → L (e b) = σb • f jb →
      c = σa * σb * s := by
    intro a b hab ja jb σa σb ha hb hLa hLb
    have h1 : inner ℝ (L (e a)) (L (e b)) = c := by
      rw [LinearIsometryEquiv.inner_map_map]; exact hcne a b hab
    rw [hLa, hLb, real_inner_smul_left, real_inner_smul_right] at h1
    by_cases hj : ja = jb
    · subst hj
      have hff : inner ℝ (f ja) (f ja) = 1 := by
        have := congrFun (congrFun hf ja) ja
        simpa [ipGram, gram] using this
      rw [hff] at h1
      exfalso
      rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
      · nlinarith [show ((m + 2 : ℕ) : ℝ) ≥ 0 from Nat.cast_nonneg _]
      · push_cast at hlo; nlinarith
      · push_cast at hlo; nlinarith
      · nlinarith [show ((m + 2 : ℕ) : ℝ) ≥ 0 from Nat.cast_nonneg _]
    · have hfs : inner ℝ (f ja) (f jb) = s := by
        have := congrFun (congrFun hf ja) jb
        simpa [ipGram, gram, hj] using this
      rw [hfs] at h1
      linarith
  obtain ⟨j0, σ0, h0, e0⟩ := edge_to_signed_edge e f hLe hLf T hT 0
  obtain ⟨j1, σ1, h1, e1⟩ := edge_to_signed_edge e f hLe hLf T hT 1
  obtain ⟨j2, σ2, h2, e2⟩ := edge_to_signed_edge e f hLe hLf T hT 2
  have n01 : (0 : Fin (m + 3)) ≠ 1 := by
    intro h; have := congrArg Fin.val h; rw [Fin.val_zero, Fin.val_one] at this; omega
  have n02 : (0 : Fin (m + 3)) ≠ 2 := by
    intro h; have := congrArg Fin.val h; rw [Fin.val_zero, Fin.val_two] at this; omega
  have n12 : (1 : Fin (m + 3)) ≠ 2 := by
    intro h; have := congrArg Fin.val h; rw [Fin.val_one, Fin.val_two] at this; omega
  have k01 := key 0 1 n01 j0 j1 σ0 σ1 h0 h1 e0 e1
  have k02 := key 0 2 n02 j0 j2 σ0 σ2 h0 h2 e0 e2
  have k12 := key 1 2 n12 j1 j2 σ1 σ2 h1 h2 e1 e2
  rcases h0 with rfl | rfl <;> rcases h1 with rfl | rfl <;> rcases h2 with rfl | rfl <;>
    linarith

/-- **The contrast in dimension two.**  `R_2(c)` and `R_2(-c)` are congruent by an isometry of the
plane, so in dimension two the parameter is not determined by congruence class. -/
theorem congruent_two_neg (e : Fin 2 → V 2) :
    ∃ T : V 2 ≃ᵃⁱ[ℝ] V 2, T '' parallelepiped (flip2 e) = parallelepiped e :=
  ⟨AffineIsometryEquiv.constVAdd ℝ (V 2) (e 1), by
    have h : ⇑(AffineIsometryEquiv.constVAdd ℝ (V 2) (e 1)) = fun x => x + e 1 := by
      funext x; simp [add_comm]
    rw [h]; exact parallelepiped_flip2 e⟩

end CubicRhombus
