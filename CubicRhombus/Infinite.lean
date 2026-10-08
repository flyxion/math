import Mathlib
import CubicRhombus.Gram
import CubicRhombus.Theorems
import CubicRhombus.Expansion

/-!
# S09 to S14: the infinite dimensional rhombus

An infinite cubic rhombus system is a family `e : ℕ → E` of unit vectors with all pairwise inner
products equal to `c`.  The finite sections are the families `Fin (n+1) → E`.

* S09: such systems exist in `ℓ²` for `0 ≤ c ≤ 1`; the Gram form is unbounded on finite sections
  when `c > 0`.
* S10: the volume of the `n`-th section tends to `1` at `c = 0` and to `0` on `(0,1)`.
* S11: the quadratic coefficient `-n(n+1)/2` of the log volume diverges.
* S12: for `0 ≤ c < 1` the system is linearly independent, hence lies in no finite dimensional space.
* S14: the limiting volume is constant on `(0,1)`.
-/

open Filter Topology

namespace CubicRhombus

/-- An infinite cubic rhombus system with parameter `c`. -/
def IsSystem {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] (e : ℕ → E) (c : ℝ) : Prop :=
  ∀ i j, inner ℝ (e i) (e j) = if i = j then (1 : ℝ) else c

/-! ### S10 and S14: limiting volume -/

theorem tendsto_vol2_zero {c : ℝ} (h0 : 0 < c) (h1 : c < 1) :
    Tendsto (fun n : ℕ => vol2 n c) atTop (𝓝 0) := by
  have ha : 0 ≤ 1 - c := by linarith
  have hb : 1 - c < 1 := by linarith
  have t1 := tendsto_pow_atTop_nhds_zero_of_lt_one ha hb
  have t2 := tendsto_self_mul_const_pow_of_lt_one ha hb
  have t3 := t1.add (t2.const_mul c)
  simp only [mul_zero, add_zero] at t3
  refine t3.congr fun n => ?_
  unfold vol2; ring

theorem tendsto_vol2_at_cube (n : ℕ) : vol2 n 0 = 1 := vol2_zero n

/-- **S10.**  The limiting volume is `1` only at the cube: if `vol2 n c → ℓ` with `0 ≤ c < 1` and
`ℓ = 1` then `c = 0`. -/
theorem limit_volume_eq_one {c ℓ : ℝ} (h0 : 0 ≤ c) (h1 : c < 1)
    (hl : Tendsto (fun n : ℕ => vol2 n c) atTop (𝓝 ℓ)) (hℓ : ℓ = 1) : c = 0 := by
  by_contra hne
  have hc : 0 < c := lt_of_le_of_ne h0 (Ne.symm hne)
  have := tendsto_nhds_unique hl (tendsto_vol2_zero hc h1)
  rw [hℓ] at this
  exact one_ne_zero this

/-- **S14.**  The limiting volume is the same for any two parameters in `(0,1)`, so the limiting
volume does not determine `c`. -/
theorem limit_volume_not_injective :
    ∃ c c' : ℝ, c ≠ c' ∧ 0 < c ∧ c < 1 ∧ 0 < c' ∧ c' < 1 ∧
      Tendsto (fun n : ℕ => vol2 n c) atTop (𝓝 0) ∧
      Tendsto (fun n : ℕ => vol2 n c') atTop (𝓝 0) :=
  ⟨1 / 3, 1 / 2, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num,
    tendsto_vol2_zero (by norm_num) (by norm_num), tendsto_vol2_zero (by norm_num) (by norm_num)⟩

/-! ### S11: divergence of the quadratic coefficient -/

theorem quadratic_coeff_diverges :
    Tendsto (fun n : ℕ => -((n : ℝ) * (n + 1) / 2)) atTop atBot := by
  refine tendsto_atBot.mpr fun b => ?_
  filter_upwards [eventually_ge_atTop (⌈-b⌉₊ + 1)] with n hn
  have h1 : (⌈-b⌉₊ : ℝ) + 1 ≤ n := by exact_mod_cast hn
  have h2 : -b ≤ ⌈-b⌉₊ := Nat.le_ceil _
  have h3 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  nlinarith

/-! ### S12: linear independence -/

theorem inner_sum_system {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {e : ℕ → E} {c : ℝ} (he : IsSystem e c) (s : Finset ℕ) (g : ℕ → ℝ) :
    inner ℝ (∑ i ∈ s, g i • e i) (∑ j ∈ s, g j • e j) =
      (1 - c) * ∑ i ∈ s, g i ^ 2 + c * (∑ i ∈ s, g i) ^ 2 := by
  have he' : ∀ i j, inner ℝ (e j) (e i) = if i = j then (1 : ℝ) else c := by
    intro i j
    have := he j i
    rw [this]
    simp only [eq_comm]
  simp only [sum_inner, inner_sum, real_inner_smul_left, real_inner_smul_right, he']
  have : ∀ i ∈ s, ∑ j ∈ s, g i * (g j * (if i = j then (1 : ℝ) else c)) =
      (1 - c) * g i ^ 2 + c * g i * ∑ j ∈ s, g j := by
    intro i hi
    have : ∀ j ∈ s, g i * (g j * (if i = j then (1 : ℝ) else c)) =
        (1 - c) * (if i = j then g i ^ 2 else 0) + c * g i * g j := by
      intro j hj
      by_cases h : i = j
      · subst h; simp; ring
      · simp [h]; ring
    rw [Finset.sum_congr rfl this, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
    simp [hi]
  rw [Finset.sum_congr rfl this, Finset.sum_add_distrib, ← Finset.mul_sum]
  rw [← Finset.sum_mul, ← Finset.mul_sum]
  ring

/-- **S12.**  For `0 ≤ c < 1` an infinite cubic rhombus system is linearly independent. -/
theorem system_linearIndependent {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {e : ℕ → E} {c : ℝ} (he : IsSystem e c) (h0 : 0 ≤ c) (h1 : c < 1) :
    LinearIndependent ℝ e := by
  rw [linearIndependent_iff']
  intro s g hg i hi
  have h := inner_sum_system he s g
  rw [hg, inner_zero_left] at h
  have hsum : ∑ j ∈ s, g j ^ 2 = 0 := by
    have : 0 ≤ c * (∑ j ∈ s, g j) ^ 2 := by positivity
    have hpos : 0 ≤ ∑ j ∈ s, g j ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
    have : 0 < 1 - c := by linarith
    nlinarith
  have := (Finset.sum_eq_zero_iff_of_nonneg (fun _ _ => sq_nonneg _)).mp hsum i hi
  exact pow_eq_zero_iff (two_ne_zero) |>.mp this

/-- The system lies in no finite dimensional subspace. -/
theorem system_not_finite_dim {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {e : ℕ → E} {c : ℝ} (he : IsSystem e c) (h0 : 0 ≤ c) (h1 : c < 1)
    (W : Submodule ℝ E) (hW : ∀ i, e i ∈ W) : ¬ FiniteDimensional ℝ W := by
  intro hfin
  have hli := system_linearIndependent he h0 h1
  have : LinearIndependent ℝ (fun i => (⟨e i, hW i⟩ : W)) :=
    LinearIndependent.of_comp W.subtype hli
  have := this.finite
  exact not_finite ℕ

/-! ### S09: existence in `ℓ²`, and unboundedness of the Gram form -/

/-- The Hilbert space `ℓ²` over the index set `Option ℕ`; the point `none` carries the common
component and `some i` carries the private component of the `i`-th vector. -/
abbrev L2 := lp (fun _ : Option ℕ => ℝ) 2

/-- The `i`-th vector `√c · u + √(1-c) · b_i`. -/
noncomputable def sysVec (c : ℝ) (i : ℕ) : L2 :=
  Real.sqrt c • lp.single 2 none (1 : ℝ) + Real.sqrt (1 - c) • lp.single 2 (some i) (1 : ℝ)

theorem ip_single (a b : ℝ) (i j : Option ℕ) :
    inner ℝ (a • lp.single 2 i (1 : ℝ) : L2) (b • lp.single 2 j (1 : ℝ)) =
      a * b * (if i = j then 1 else 0) := by
  rw [real_inner_smul_left, real_inner_smul_right, lp.inner_single_left]
  simp [lp.single_apply]
  split_ifs <;> simp_all

/-- **S09, existence.**  For `0 ≤ c ≤ 1` there is an infinite system of unit vectors in `ℓ²` with
all pairwise inner products equal to `c`. -/
theorem sysVec_isSystem {c : ℝ} (h0 : 0 ≤ c) (h1 : c ≤ 1) : IsSystem (sysVec c) c := by
  intro i j
  have a := Real.mul_self_sqrt h0
  have b := Real.mul_self_sqrt (sub_nonneg.mpr h1)
  unfold sysVec
  rw [inner_add_left, inner_add_right, inner_add_right, ip_single, ip_single, ip_single,
    ip_single]
  by_cases h : i = j
  · subst h; simp; nlinarith
  · simp [h]; nlinarith

/-- **S09, unboundedness.**  For `c > 0` the quadratic form of the Gram matrix is unbounded on
finite sections: on the all ones vector its Rayleigh quotient is `1 + n c`. -/
theorem gram_form_unbounded {c : ℝ} (hc : 0 < c) (M : ℝ) :
    ∃ n : ℕ, M * ((n : ℝ) + 1) <
      (fun _ : Fin (n + 1) => (1 : ℝ)) ⬝ᵥ (gram (n + 1) c).mulVec (fun _ => 1) := by
  obtain ⟨n, hn⟩ := exists_nat_gt ((M - 1) / c)
  refine ⟨n, ?_⟩
  rw [quadForm_gram]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, one_pow, mul_one]
  push_cast
  have h1 : (M - 1) < c * n := by
    have := (div_lt_iff₀ hc).mp hn; linarith
  nlinarith [Nat.cast_nonneg (α := ℝ) n]

end CubicRhombus
