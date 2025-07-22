/-
Copyright (c) 2024 Joseph Myers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Myers
-/
import Batteries.Data.Nat.Gcd
import Mathlib.Data.Nat.Lattice

namespace IMOSL2024A8

-- This is to be determined by the solver of the original problem.
def solutionSet : Set (ℕ → ℕ) := {a | ∃ c, 0 < c ∧ a = (· + c)}

theorem result {p q : ℕ} (hp : 0 < p) (hq : 0 < q) (hne : p ≠ q) (hc : Nat.Coprime p q)
    {a : ℕ → ℕ} (hapos : ∀ i, 0 < a i) :
    (∀ n, ((⨆ i ∈ Finset.Icc n (n + p), a i) - ⨅ i ∈ Finset.Icc n (n + p), a i = p) ∧
      ((⨆ i ∈ Finset.Icc n (n + q), a i) - ⨅ i ∈ Finset.Icc n (n + q), a i = q)) ↔
      a ∈ solutionSet := by
  sorry

end IMOSL2024A8
