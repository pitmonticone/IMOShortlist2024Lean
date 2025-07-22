/-
Copyright (c) 2024 Joseph Myers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Myers
-/
import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Nat.Dist

namespace IMOSL2024C6

-- The marbles on one side of the balance (weights 1 more than the `Fin n` values)
abbrev Config (n : ℕ) := Finset (Fin (4 * n))

namespace Config

open scoped symmDiff

variable {n : ℕ} (c : Config n)

def weight : ℕ := ∑ i ∈ c, ((i : ℕ) + 1)

def weightDiff : ℕ := Nat.dist c.weight cᶜ.weight

def ValidMove (c₂ : Config n) : Prop := (c ∆ c₂).card = 1

def ValidMoveSeq (c₂ : Config n) (T : ℕ) (x : List (Config n)) : Prop :=
  ∃ h : x ≠ [], x.head h = c ∧ x.getLast h = c₂ ∧ x.Chain' ValidMove ∧ ∀ c' ∈ x, c'.weightDiff ≤ T

def CanMove (c₂ : Config n) (T : ℕ) : Prop := ∃ x : List (Config n), c.ValidMoveSeq c₂ T x

end Config

-- This is to be determined by the solver of the original problem.
def answer (n : ℕ) : ℕ := 4 * n

theorem result (n : ℕ) (h : 0 < n) :
    (∀ c : Config n, c.weightDiff = 0 → c.CanMove cᶜ (answer n)) ∧
    ∀ T < answer n, ∃ c : Config n, c.weightDiff = 0 ∧ ¬c.CanMove cᶜ T := by
  sorry

end IMOSL2024C6
