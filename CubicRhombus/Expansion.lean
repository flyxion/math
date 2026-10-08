import Mathlib
import CubicRhombus.Gram

/-!
# S03 / T4: expansion of the log volume at the cube

`log vol2 n c = -(n (n+1) / 2) c^2 + (n (n^2 - 1) / 3) c^3 + O(c^4)`, with an explicit constant.
-/

namespace CubicRhombus

/-- The cubic Taylor polynomial of `log vol2 n` at `0`. -/
noncomputable def logExp (n : ℕ) (c : ℝ) : ℝ :=
  -((n : ℝ) * (n + 1) / 2) * c ^ 2 + ((n : ℝ) * ((n : ℝ) ^ 2 - 1) / 3) * c ^ 3

private lemma log_one_sub_bound {x : ℝ} (hx : |x| ≤ 1 / 2) :
    |x + x ^ 2 / 2 + x ^ 3 / 3 + Real.log (1 - x)| ≤ 2 * x ^ 4 := by
  have h1 : |x| < 1 := by linarith
  have := Real.abs_log_sub_add_sum_range_le h1 3
  simp [Finset.sum_range_succ] at this
  have h2 : |x| ^ 4 / (1 - |x|) ≤ 2 * x ^ 4 := by
    have hp : 0 < 1 - |x| := by linarith
    rw [div_le_iff₀ hp]
    have : |x| ^ 4 = x ^ 4 := by
      rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, sq_abs, ← pow_mul]
    rw [this]
    have h4 : 0 ≤ x ^ 4 := by positivity
    nlinarith
  have e : x + x ^ 2 / 2 + x ^ 3 / 3 + Real.log (1 - x) =
      x + x ^ 2 / 2 + x ^ 3 / 3 + Real.log (1 - x) := rfl
  calc _ ≤ |x| ^ 4 / (1 - |x|) := by
        convert this using 2; norm_num
    _ ≤ _ := h2

/-- **T4, explicit form.**  For `|c| ≤ 1 / (2 (n+1))` the cubic Taylor polynomial approximates
`log (vol2 n c)` to within `(2 n + 2 n^4) c^4`. -/
theorem log_vol2_expansion (n : ℕ) {c : ℝ} (hc : |c| ≤ 1 / (2 * (n + 1))) :
    |Real.log (vol2 n c) - logExp n c| ≤ (2 * n + 2 * (n : ℝ) ^ 4) * c ^ 4 := by
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hn1 : (1 : ℝ) ≤ n + 1 := by linarith
  have hc1 : |c| ≤ 1 / 2 := by
    refine hc.trans ?_
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]; nlinarith
  have hnc : |(n : ℝ) * c| ≤ 1 / 2 := by
    rw [abs_mul, abs_of_nonneg hn]
    have : (n : ℝ) * |c| ≤ n * (1 / (2 * (n + 1))) := mul_le_mul_of_nonneg_left hc hn
    refine this.trans ?_
    rw [← mul_div_assoc, mul_one, div_le_div_iff₀ (by positivity) (by norm_num)]; nlinarith
  have ha := log_one_sub_bound hc1
  have hb := log_one_sub_bound (x := -(n * c)) (by rwa [abs_neg])
  have hpos1 : 0 < 1 - c := by have := (abs_le.mp hc1).2; linarith
  have hpos2 : 0 < 1 + n * c := by have := (abs_le.mp hnc).1; linarith
  have hlog : Real.log (vol2 n c) = n * Real.log (1 - c) + Real.log (1 + n * c) := by
    unfold vol2
    rw [Real.log_mul (pow_pos hpos1 n).ne' hpos2.ne', Real.log_pow]
  have e1 : 1 - -((n : ℝ) * c) = 1 + n * c := by ring
  rw [e1] at hb
  have key : Real.log (vol2 n c) - logExp n c =
      n * (c + c ^ 2 / 2 + c ^ 3 / 3 + Real.log (1 - c)) * 1 -
      n * (c + c ^ 2 / 2 + c ^ 3 / 3) +
      ((-(n * c) + (-(n * c)) ^ 2 / 2 + (-(n * c)) ^ 3 / 3 + Real.log (1 + n * c))
        - (-(n * c) + (-(n * c)) ^ 2 / 2 + (-(n * c)) ^ 3 / 3)) - logExp n c := by
    rw [hlog]; ring
  have key2 : Real.log (vol2 n c) - logExp n c =
      n * (c + c ^ 2 / 2 + c ^ 3 / 3 + Real.log (1 - c)) +
      (-(n * c) + (-(n * c)) ^ 2 / 2 + (-(n * c)) ^ 3 / 3 + Real.log (1 + n * c)) := by
    rw [hlog]; unfold logExp; ring
  rw [key2]
  have t1 : |(n : ℝ) * (c + c ^ 2 / 2 + c ^ 3 / 3 + Real.log (1 - c))| ≤ n * (2 * c ^ 4) := by
    rw [abs_mul, abs_of_nonneg hn]
    exact mul_le_mul_of_nonneg_left ha hn
  have t2 : |-(n * c) + (-(n * c)) ^ 2 / 2 + (-(n * c)) ^ 3 / 3 + Real.log (1 + n * c)|
      ≤ 2 * (n : ℝ) ^ 4 * c ^ 4 := by
    have : 2 * (-(n * c)) ^ 4 = 2 * (n : ℝ) ^ 4 * c ^ 4 := by ring
    linarith
  calc _ ≤ |(n : ℝ) * (c + c ^ 2 / 2 + c ^ 3 / 3 + Real.log (1 - c))| +
        |-(n * c) + (-(n * c)) ^ 2 / 2 + (-(n * c)) ^ 3 / 3 + Real.log (1 + n * c)| :=
        abs_add_le _ _
    _ ≤ _ := by nlinarith

/-- Asymptotic form: the error is `O(c^4)` as `c → 0`. -/
theorem log_vol2_isBigO (n : ℕ) :
    (fun c => Real.log (vol2 n c) - logExp n c) =O[nhds 0] fun c => c ^ 4 := by
  refine Asymptotics.IsBigO.of_bound (2 * n + 2 * (n : ℝ) ^ 4) ?_
  have hε : (0 : ℝ) < 1 / (2 * (n + 1)) := by positivity
  filter_upwards [Metric.ball_mem_nhds 0 hε] with c hc
  rw [Metric.mem_ball, dist_zero_right, Real.norm_eq_abs] at hc
  have := log_vol2_expansion n hc.le
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (by positivity : (0:ℝ) ≤ c ^ 4)]
  exact this

end CubicRhombus
