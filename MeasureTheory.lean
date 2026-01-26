/-
# Step-by-Step Tactics Guide

This file shows EXACTLY what tactics to type for each proof.
Follow along in your editor!
-/

import Mathlib.Data.Real.Basic
import Mathlib.Order.Bounds.Basic
import Mathlib.Tactic

/-! ## Example 1: Proving inf ≤ sup (The Easiest One) -/

/-- Step-by-step: inf ≤ sup for bounded functions on an interval -/
example {a b : ℝ} (hab : a < b) (f : ℝ → ℝ)
    (hbdd_below : BddBelow (f '' Set.Icc a b))
    (hbdd_above : BddAbove (f '' Set.Icc a b)) :
    sInf (f '' Set.Icc a b) ≤ sSup (f '' Set.Icc a b) := by
  -- Step 1: This is exactly what csInf_le_csSup says!
  -- Type: #check csInf_le_csSup
  -- You'll see: csInf_le_csSup : BddBelow s → BddAbove s → s.Nonempty → sInf s ≤ sSup s
  
  apply csInf_le_csSup
  
  -- Now we have 3 goals. Let's prove them one by one:
  
  -- Goal 1: BddBelow (f '' Set.Icc a b)
  · exact hbdd_below
  
  -- Goal 2: BddAbove (f '' Set.Icc a b)
  · exact hbdd_above
  
  -- Goal 3: (f '' Set.Icc a b).Nonempty
  · -- We need to show the set is nonempty
    -- The interval [a,b] is nonempty (we have hab : a < b)
    -- So f '' [a,b] is also nonempty
    apply Set.Nonempty.image
    -- Now we need: Set.Icc a b is nonempty
    exact Set.nonempty_Icc.mpr (le_of_lt hab)
    -- Done!

/-! ## Example 2: Proving inf on [a,b] ≤ inf on [x,y] when [x,y] ⊆ [a,b] -/

example {a b x y : ℝ} (hab : a < b) (f : ℝ → ℝ)
    (hbdd : BddBelow (f '' Set.Icc a b))
    (hx : a ≤ x) (hy : y ≤ b) (hxy : x ≤ y) :
    sInf (f '' Set.Icc a b) ≤ sInf (f '' Set.Icc x y) := by
  -- Step 1: We want to use csInf_le_csInf
  -- Type: #check csInf_le_csInf
  -- You'll see it compares two infs when one set is a subset of another
  
  apply csInf_le_csInf
  
  -- Goal 1: BddBelow (f '' Set.Icc a b)
  · exact hbdd
  
  -- Goal 2: (f '' Set.Icc x y).Nonempty
  · apply Set.Nonempty.image
    exact Set.nonempty_Icc.mpr hxy
  
  -- Goal 3: f '' Set.Icc x y ⊆ f '' Set.Icc a b
  · -- This means: every element of f '' [x,y] is in f '' [a,b]
    intro z hz  -- Let z be in f '' [x,y]
    -- hz tells us: ∃ t ∈ [x,y], f(t) = z
    obtain ⟨t, ht, rfl⟩ := hz
    -- Now we know: z = f(t) and t ∈ [x,y]
    -- We need to show: z ∈ f '' [a,b]
    -- i.e., ∃ t' ∈ [a,b], f(t') = z
    use t  -- Use the same t!
    constructor
    · -- Show: t ∈ [a,b]
      -- We know t ∈ [x,y] and [x,y] ⊆ [a,b]
      exact Set.Icc_subset_Icc hx hy ht
    · -- Show: f(t) = z
      rfl  -- This is definitional

/-! ## Example 3: Multiplying inequalities by nonnegative numbers -/

example {a b c d w : ℝ} (h : a ≤ b) (hw : 0 ≤ w) :
    w * a ≤ w * b := by
  -- Step 1: Use the lemma for multiplying inequalities
  -- Type: #check mul_le_mul_of_nonneg_left
  
  apply mul_le_mul_of_nonneg_left
  
  -- Goal 1: a ≤ b
  · exact h
  
  -- Goal 2: 0 ≤ w
  · exact hw

/-! ## Example 4: The complete proof for one interval -/

example {a b x y : ℝ} (hab : a < b) (f : ℝ → ℝ)
    (hbdd_below : BddBelow (f '' Set.Icc a b))
    (hbdd_above : BddAbove (f '' Set.Icc a b))
    (hx : a ≤ x) (hy : y ≤ b) (hxy : x < y) :
    (y - x) * sInf (f '' Set.Icc a b) ≤ (y - x) * sInf (f '' Set.Icc x y) := by
  
  -- Strategy: Factor out (y - x) and use inf_mono_subset
  
  apply mul_le_mul_of_nonneg_left
  
  -- Goal 1: sInf (f '' Set.Icc a b) ≤ sInf (f '' Set.Icc x y)
  · apply csInf_le_csInf
    · exact hbdd_below
    · apply Set.Nonempty.image
      exact Set.nonempty_Icc.mpr (le_of_lt hxy)
    · intro z hz
      obtain ⟨t, ht, rfl⟩ := hz
      use t
      exact ⟨Set.Icc_subset_Icc hx hy ht, rfl⟩
  
  -- Goal 2: 0 ≤ y - x
  · linarith  -- Lean's linear arithmetic tactic solves this automatically!


example {a b x y z : ℝ} (hab : a < b) (f : ℝ → ℝ)
    (hbdd : BddBelow (f '' Set.Icc a b))
    (hx : a ≤ x) (hxy : x < y) (hyz : y < z) (hz : z ≤ b)
    (h1 : sInf (f '' Set.Icc x z) ≤ sInf (f '' Set.Icc x y))
    (h2 : sInf (f '' Set.Icc x z) ≤ sInf (f '' Set.Icc y z)) :
    (z - x) * sInf (f '' Set.Icc x z) ≤
    (y - x) * sInf (f '' Set.Icc x y) + (z - y) * sInf (f '' Set.Icc y z) := by
  
  -- calc is great for step-by-step inequality chains!
  calc (z - x) * sInf (f '' Set.Icc x z)
      = ((y - x) + (z - y)) * sInf (f '' Set.Icc x z) := by
        -- Show: z - x = (y - x) + (z - y)
        ring  -- The "ring" tactic solves polynomial equations!
    _ = (y - x) * sInf (f '' Set.Icc x z) + (z - y) * sInf (f '' Set.Icc x z) := by
        ring  -- Distribute
    _ ≤ (y - x) * sInf (f '' Set.Icc x y) + (z - y) * sInf (f '' Set.Icc y z) := by
        -- Add two inequalities
        apply add_le_add
        · -- First term
          apply mul_le_mul_of_nonneg_left h1
          linarith
        · -- Second term
          apply mul_le_mul_of_nonneg_left h2
          linarith

/-! ## Common Tactics Cheat Sheet -/

/-- 
Tactic Reference:

1. `exact h` - Use hypothesis h directly

2. `apply thm` - Apply theorem, creates subgoals for its hypotheses

3. `intro x` - Introduce a variable or hypothesis

4. `obtain ⟨x, h⟩ := ...` - Destructure existential or conjunction

5. `use x` - Provide witness for existential

6. `constructor` - Split ∧ into two goals

7. `left` / `right` - Choose side of ∨

8. `linarith` - Solve linear arithmetic (inequalities, equations)

9. `ring` - Solve polynomial equations

10. `simp` - Simplify using simplification lemmas

11. `rfl` - Prove by reflexivity (x = x, or definitional equality)

12. `calc` - Write step-by-step calculation

13. `by_cases h : P` - Case split on whether P is true

14. `have h : P := ...` - Create intermediate fact

Common patterns:

- Proving subset: `intro x hx; <show x in target>`
- Proving inequality: `apply some_le_lemma; <prove hypotheses>`
- Destructuring ∃: `obtain ⟨x, hx, h⟩ := ...`
- Showing nonempty set: `use x; <show x in set>`
-/

