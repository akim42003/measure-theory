
import Mathlib

/-!
# Hoeffding Bound Arithmetic Verification

Goal: For ε = δ = 0.05, verify that n = 738 satisfies
  2 * exp(-2n * ε²) ≤ δ

This reduces to showing:
  2 * exp(-2 * 738 * 0.0025) ≤ 0.05
  2 * exp(-3.69) ≤ 0.05
  exp(-3.69) ≤ 0.025

Equivalently (since exp is monotone):
  exp(3.69) ≥ 40

Strategy: Use the Taylor lower bound
  exp(x) ≥ 1 + x + x²/2 + x³/6 + x⁴/24
  and show this exceeds 40 at x = 3.69.
-/

-- Step 1: The algebraic reduction
-- 2 * 738 * (0.05)^2 = 738 * 0.005 = 3.69
theorem epsilon_delta_algebra :
    2 * 738 * (0.05 : ℝ)^2 = 3.69 := by
  norm_num

-- Step 2: Taylor lower bound for exp
-- exp(x) ≥ 1 + x + x²/2 + x³/6 + x⁴/24 for x ≥ 0
theorem exp_taylor_lower_bound (x : ℝ) (hx : 0 ≤ x) :
    1 + x + x^2 / 2 + x^3 / 6 + x^4 / 24 ≤ Real.exp x := by
  have := Real.sum_le_exp_of_nonneg hx 5
  -- Expand the partial sum and match terms
  simp [Finset.sum_range_succ, Nat.factorial] at this
  linarith

-- Step 3: The Taylor polynomial at 3.69 exceeds 40
theorem taylor_at_369_ge_40 :
    1 + 3.69 + (3.69 : ℝ)^2 / 2 + 3.69^3 / 6 + 3.69^4 / 24 ≥ 40 := by
  norm_num

-- Step 4: Therefore exp(3.69) ≥ 40
theorem exp_369_ge_40 : Real.exp 3.69 ≥ 40 := by
  have h1 := exp_taylor_lower_bound 3.69 (by norm_num)
  have h2 := taylor_at_369_ge_40
  linarith

-- Step 5: Therefore exp(-3.69) ≤ 1/40 = 0.025
theorem exp_neg_369_le : Real.exp (-3.69) ≤ 0.025 := by
  rw [Real.exp_neg]
  have h := exp_369_ge_40
  rw [inv_le (by linarith : (0:ℝ) < Real.exp 3.69) (by norm_num)]
  linarith

-- Step 6: Final result — 2 * exp(-2 * 738 * 0.05²) ≤ 0.05
theorem hoeffding_bound_n738 :
    2 * Real.exp (-(2 * 738 * (0.05 : ℝ)^2)) ≤ 0.05 := by
  have halg : 2 * 738 * (0.05 : ℝ)^2 = 3.69 := by norm_num
  rw [show (2 : ℝ) * 738 * 0.05^2 = 3.69 from by norm_num]
  have h := exp_neg_369_le
  linarith
