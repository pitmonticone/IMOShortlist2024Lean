/-
Copyright (c) 2024 Joseph Myers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Myers
-/
import Mathlib.Algebra.Ring.Periodic
import Mathlib.Data.Real.Basic

namespace IMOSL2024A5

-- This is to be determined by the solver of the original problem.
def solutionSet : Set (ℕ → ℝ) :=
  {a | (∃ c : ℝ, c ∈ Set.Icc (-1 / 2) (1 / 2) ∧ a = fun n ↦ (-1) ^ n * c) ∨
    (∃ d : ℝ, a = Function.const _ d)}

theorem result (a : ℕ → ℝ) :
    ((∃ k : ℕ, 0 < k ∧ Function.Periodic a k) ∧
      ∀ n : ℕ, a (n + 2) + (a n) ^ 2 = a n + a (n + 1) ^ 2 ∧ |a (n + 1) - a n| ≤ 1) ↔
    a ∈ solutionSet := by
  sorry

end IMOSL2024A5
