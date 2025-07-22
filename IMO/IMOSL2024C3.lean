/-
Copyright (c) 2024 Joseph Myers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Myers
-/
import Mathlib.Data.Fin.Basic
import Mathlib.Logic.Equiv.Defs

namespace IMOSL2024C3

-- A configuration of knights is represented as a map from knights to places at the table.
-- Knights 2m and 2m+1 are lovers.

def ValidExchanges {n m : ℕ} [NeZero m] [NeZero (2 * n)]
    (seatings : Fin m → Equiv.Perm (Fin (2 * n))) : Prop :=
  ∀ i : Fin m, i < m - 1 →
    ∃ k : Fin (2 * n), seatings (i + 1) = (seatings i).trans (Equiv.swap k (k + 1))

def Adjacent {n : ℕ} [NeZero (2 * n)] (a b : Fin (2 * n)) : Prop := a - b = 1 ∨ b - a = 1

def CanShakeHands {n : ℕ} [NeZero (2 * n)] (seating : Equiv.Perm (Fin (2 * n))) (k : Fin n) :
    Prop :=
  Adjacent (seating ⟨(2 * (k : ℕ) : ℕ), by omega⟩) (seating ⟨(2 * (k : ℕ) + 1 : ℕ), by omega⟩)

def AllShakeHands {n m : ℕ} [NeZero m] [NeZero (2 * n)]
    (seatings : Fin m → Equiv.Perm (Fin (2 * n))) : Prop :=
  ∀ i : Fin n, ∃ k, CanShakeHands (seatings k) i

def CanAllSwapIn {n : ℕ} [NeZero (2 * n)] (m : ℕ) (seating : Equiv.Perm (Fin (2 * n))) : Prop :=
  ∃ seatings : Fin (m + 1) → Equiv.Perm (Fin (2 * n)),
    seatings 0 = seating ∧ ValidExchanges seatings ∧ AllShakeHands seatings

-- This is to be determined by the solver of the original problem.
def answer (n : ℕ) : ℕ := n * (n - 1) / 2

theorem result (n : ℕ) [NeZero (2 * n)] :
  (∀ seating : Equiv.Perm (Fin (2 * n)), CanAllSwapIn (answer n) seating) ∧
    ∀ m < answer n, ¬ ∀ seating : Equiv.Perm (Fin (2 * n)), CanAllSwapIn m seating := by
  sorry

end IMOSL2024C3
