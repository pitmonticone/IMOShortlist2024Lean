/-
Copyright (c) 2024 Joseph Myers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Myers
-/
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Tactic.Positivity

namespace IMOSL2024A2

-- Following Solution 2.

def xmap (n : ℕ) : ℕ ↪ ℕ where
  toFun := fun m ↦ 2 ^ n * (2 * m + 1)
  inj' := fun x y h ↦ by
    dsimp only at h
    rw [Nat.mul_right_inj (by simp), add_left_inj, Nat.mul_right_inj (by simp)] at h
    exact h

def x_to_finset {n : ℕ} (x : Fin (n + 1) → ℕ) : Finset ℕ :=
  Finset.univ.biUnion fun i ↦ (Finset.range (x i)).map (xmap i)

lemma disjoint_xmap {n : ℕ} (x : Fin (n + 1) → ℕ)
    (s : Finset (Fin (n + 1))) : Set.PairwiseDisjoint ↑s
      fun i ↦ (Finset.range (x i)).map (xmap i) := by
  intro i hi j hj hij s hsi hsj
  simp only [Finset.le_eq_subset, Finset.bot_eq_empty] at hsi hsj ⊢
  calc s ⊆ (Finset.range (x i)).map (xmap i) ∩ (Finset.range (x j)).map (xmap j) :=
      Finset.subset_inter hsi hsj
    _ = ∅ := by
      ext y
      simp only [Finset.mem_inter, Finset.mem_map, Finset.mem_range, Finset.notMem_empty,
                 iff_false, not_and, not_exists, forall_exists_index, and_imp]
      rintro xi - hxy yi - hxy'
      simp only [xmap, Function.Embedding.coeFn_mk] at hxy hxy'
      sorry
    _ ⊆ ∅ := Finset.Subset.refl _

lemma card_x_to_finset {n : ℕ} (x : Fin (n + 1) → ℕ) : (x_to_finset x).card = ∑ i, x i := by
  sorry

lemma zero_not_mem_x_to_finset {n : ℕ} (x : Fin (n + 1) → ℕ) : 0 ∉ (x_to_finset x) := by
  simp only [x_to_finset, xmap, Finset.mem_biUnion, Finset.mem_univ, Finset.mem_map,
             Finset.mem_range, Function.Embedding.coeFn_mk, true_and, not_exists, not_and]
  intro i _ _
  positivity

lemma sum_two_pow_mul_sq {n : ℕ} (x : Fin (n + 1) → ℕ) :
    ∑ i : Fin (n + 1), 2 ^ (i : ℕ) * x i ^ 2 = ∑ i ∈ (x_to_finset x), i := by
  sorry

lemma le_sum_two_pow_mul_sq {n : ℕ} (x : Fin (n + 1) → ℕ) :
    (∑ i, x i) * ((∑ i, x i) + 1) / 2 ≤ ∑ i : Fin (n + 1), 2 ^ (i : ℕ) * x i ^ 2 := by
  rw [sum_two_pow_mul_sq, ← card_x_to_finset]
  sorry

def optimal_x (n : ℕ) (i : Fin (n + 1)) : ℕ := (n + 2 ^ (i : ℕ)) / 2 ^ ((i : ℕ) + 1)

lemma optimal_x_to_finset {n : ℕ} : x_to_finset (optimal_x n) = Finset.Icc 1 n := by
  sorry

lemma sum_optimal_x (n : ℕ) : ∑ i, optimal_x n i = n := by
  sorry

lemma sum_two_pow_mul_sq_optimal_x (n : ℕ) :
    ∑ i : Fin (n + 1), 2 ^ (i : ℕ) * optimal_x n i ^ 2 = n * (n + 1) / 2 := by
  have h : insert 0 (Finset.Icc 1 n) = Finset.Icc 0 n := by
    rw [← zero_add 1, Finset.insert_Icc_add_one_left_eq_Icc n.zero_le]
  rw [sum_two_pow_mul_sq, optimal_x_to_finset, ← Finset.sum_insert_zero rfl (a := 0), h,
      ← Finset.Ico_succ_right_eq_Icc, Order.succ_eq_add_one, ← Finset.range_eq_Ico,
      Finset.sum_range_id, mul_comm, Nat.add_sub_cancel]

-- This is to be determined by the solver of the original problem.
def answer (n : ℕ) : ℕ := n * (n + 1) / 2

-- This statement allows n = 0, not allowed in the original problem.
theorem result (n : ℕ) : (∀ x : Fin (n + 1) → ℕ, ∑ i, x i = n → answer n ≤
      ∑ i : Fin (n + 1), 2 ^ (i : ℕ) * x i ^ 2) ∧
    ∃ x : Fin (n + 1) → ℕ, ∑ i, x i = n ∧
      ∑ i : Fin (n + 1), 2 ^ (i : ℕ) * x i ^ 2 = answer n := by
  refine ⟨fun x h ↦ ?_, optimal_x n, sum_optimal_x n, sum_two_pow_mul_sq_optimal_x n⟩
  convert le_sum_two_pow_mul_sq x using 1
  rw [h]
  rfl

end IMOSL2024A2
