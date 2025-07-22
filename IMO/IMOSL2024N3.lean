/-
Copyright (c) 2024 Joseph Myers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Myers
-/
import Mathlib.Analysis.SpecialFunctions.Pow.Real

namespace IMOSL2024N3

-- This is to be determined by the solver of the original problem.
def solutionSet : Set (ℕ → ℕ) := {a | ∃ c, 0 < c ∧ a = Function.const _ c}

theorem result {a : ℕ → ℕ} (ha : ∀ n, 0 < a n) :
    (∀ m n, m ≤ n → ((∃ c : ℤ, (∑ i ∈ Finset.Icc m n, a i) / (n - m + 1 : ℝ) = c) ∧
      (∃ c : ℤ, (∏ i ∈ Finset.Icc m n, a i : ℝ) ^ (1 / (n - m + 1) : ℝ) = c))) ↔
    a ∈ solutionSet := by
  sorry

end IMOSL2024N3
