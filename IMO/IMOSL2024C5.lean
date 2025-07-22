/-
Copyright (c) 2024 Joseph Myers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Myers
-/
import Mathlib.Data.Int.Interval
import Mathlib.SetTheory.Game.State

namespace IMOSL2024C5

open SetTheory SetTheory.PGame

abbrev Board := Finset ℤ

-- The valid moves from a position.  The shortlist problem uses the misère play convention
-- (last player to move loses); mathlib uses the normal play convention (player unable to move
-- loses), so express the game in those terms by making a move that would empty the board
-- invalid rather than losing.
def moves (S : Board) : Set (ℕ × ℤ) := {x | x.2 ∈ S ∧ ∃ s ∈ S, ¬ 2 ^ x.1 ∣ x.2 - s}

def move (S : Board) (m : ℕ × ℤ) := S.filter (fun s ↦ ¬ 2 ^ m.1 ∣ m.2 - s)

lemma move_ssubset {S : Board} {m : ℕ × ℤ} (h : m ∈ moves S) : move S m ⊂ S := by
  simp_rw [move, Finset.filter_ssubset]
  refine ⟨m.2, h.1, ?_⟩
  simp

noncomputable instance (S : Board) : DecidablePred fun x ↦ ∃ m ∈ moves S, move S m = x :=
  Classical.decPred _

noncomputable def next_positions (S : Board) : Finset Board :=
  S.powerset.filter (fun x ↦ ∃ m ∈ moves S, move S m = x)

noncomputable instance state : State (Board) where
  turnBound s := s.card
  l s := next_positions s
  r s := next_positions s
  left_bound m := by
    simp only [next_positions, Finset.mem_filter, Finset.mem_powerset] at m
    rcases m with ⟨-, m, hm, rfl⟩
    exact Finset.card_lt_card (move_ssubset hm)
  right_bound m := by
    simp only [next_positions, Finset.mem_filter, Finset.mem_powerset] at m
    rcases m with ⟨-, m, hm, rfl⟩
    exact Finset.card_lt_card (move_ssubset hm)

noncomputable def this_game (S : Board) : PGame :=
  PGame.ofState S

-- This is to be determined by the solver of the original problem.
def solutionSet : Set ℕ :=
  {n : ℕ | (∃ m : ℕ, Odd m ∧ n = 2 ^ m) ∨ (∃ m t : ℕ, Even m ∧ Odd t ∧ n = t * 2 ^ m)}

theorem result {N : ℕ} (h : 0 < N) :
    this_game (Finset.Icc (1 : ℤ) (N : ℤ)) ‖ 0 ↔ N ∈ solutionSet := by
  sorry

end IMOSL2024C5
