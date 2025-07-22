/-
Copyright (c) 2024 Joseph Myers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Myers
-/
import Mathlib.Algebra.Polynomial.Degree.Definitions
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Data.ZMod.Defs

namespace IMOSL2024N6

open scoped Polynomial

def Good (n : ℕ) (P : ℤ[X]) : Prop :=
  ∃ Q : ℤ[X], Q.natDegree = 2 ∧ ¬ ∃ k : ZMod n, (Q * (P + Q)).eval₂ (Int.castRingHom _) k = 0

-- This is to be determined by the solver of the original problem.
def solutionSet : Set ℕ := {n | 2 < n}

theorem result {n : ℕ} (hn : 0 < n) : (∀ P : ℤ[X], Good n P) ↔ n ∈ solutionSet := by
  sorry

end IMOSL2024N6
