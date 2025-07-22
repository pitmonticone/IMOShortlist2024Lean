/-
Copyright (c) 2024 Joseph Myers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Myers
-/
import Mathlib.Data.Fintype.Prod
import Mathlib.Order.Interval.Finset.Fin

namespace IMOSL2024C8

-- A 2x2 sub-board; only valid if the coordinates do not move across the edge of the board.
def subBoard {n : ℕ} [NeZero n] (x y : Fin n) : Finset (Fin n × Fin n) :=
  Finset.Icc x (x + 1) ×ˢ Finset.Icc y (y + 1)

def ValidSubBoard {n : ℕ} [NeZero n] (x y : Fin n) : Prop := x < n - 1 ∧ y < n - 1

def ValidMove {n : ℕ} [NeZero n] (c₁ c₂ : Finset (Fin n × Fin n)) : Prop :=
  c₁ ⊆ c₂ ∧ ∃ x y : Fin n, ValidSubBoard x y ∧
    (c₂ \ c₁) ⊆ subBoard x y ∧ (c₁ ∩ subBoard x y).card = 1 ∧ (c₂ ∩ subBoard x y).card = 4

def ValidMoveSeq {n : ℕ} [NeZero n] (x : List (Finset (Fin n × Fin n))) : Prop :=
  ∃ h : x ≠ [], x.head h = {(0, 0)} ∧ x.getLast h = Finset.univ ∧ x.Chain' ValidMove

-- This is to be determined by the solver of the original problem.
def solutionSet : Set ℕ := {n | ∃ m, n = 2 ^ m}

theorem result (n : ℕ) [NeZero n] :
    (∃ x : List (Finset (Fin n × Fin n)), ValidMoveSeq x) ↔ n ∈ solutionSet := by
  sorry

end IMOSL2024C8
