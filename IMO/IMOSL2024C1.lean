/-
Copyright (c) 2024 Joseph Myers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Myers
-/
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.GroupWithZero.Canonical
import Mathlib.Algebra.Order.Ring.Int
import Mathlib.Data.Int.ConditionallyCompleteOrder
import Mathlib.Order.ConditionallyCompleteLattice.Indexed
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

namespace IMOSL2024C1

-- The arguments r map a race number to a student number to a (0-based) place in the race.

def HasRating {n : ℕ} (a b : ℕ) (r : Fin n → Equiv.Perm (Fin n)) (s : Fin n) : Prop :=
  0 < a ∧ 0 < b ∧ a ≤ ((Finset.univ : Finset (Fin n)).filter (fun i ↦ (r i s : ℕ) < b)).card

noncomputable def score {n : ℕ} (r : Fin n → Equiv.Perm (Fin n)) (s : Fin n) : ℤ :=
  ⨆ (ab : {x : ℕ × ℕ // HasRating x.1 x.2 r s}), ((ab : ℕ × ℕ).1 : ℤ) - ((ab : ℕ × ℕ).2 : ℤ)

-- Following Solution 3 (but with weights scaled by n to avoid division).

lemma HasRating.a_pos {n a b : ℕ} {r : Fin n → Equiv.Perm (Fin n)} {s : Fin n}
    (h : HasRating a b r s) : 0 < a :=
  h.1

lemma HasRating.b_pos {n a b : ℕ} {r : Fin n → Equiv.Perm (Fin n)} {s : Fin n}
    (h : HasRating a b r s) : 0 < b :=
  h.2.1

lemma HasRating.a_le_card {n a b : ℕ} {r : Fin n → Equiv.Perm (Fin n)} {s : Fin n}
    (h : HasRating a b r s) :
    a ≤ ((Finset.univ : Finset (Fin n)).filter (fun i ↦ (r i s : ℕ) < b)).card :=
  h.2.2

lemma HasRating.a_le_n {n a b : ℕ} {r : Fin n → Equiv.Perm (Fin n)} {s : Fin n}
    (h : HasRating a b r s) : a ≤ n :=
  calc a ≤ ((Finset.univ : Finset (Fin n)).filter (fun i ↦ (r i s : ℕ) < b)).card := h.a_le_card
    _ ≤ Finset.univ.card := Finset.card_filter_le _ _
    _ = n := by simp

lemma HasRating.sub_le {n a b : ℕ} {r : Fin n → Equiv.Perm (Fin n)} {s : Fin n}
    (h : HasRating a b r s) : (a : ℤ) - (b : ℤ) ≤ n - 1 := by
  have ha := h.b_pos
  have hb := h.a_le_n
  omega

lemma HasRating.le_score {n a b : ℕ} {r : Fin n → Equiv.Perm (Fin n)} {s : Fin n}
    (h : HasRating a b r s) : (a : ℤ) - (b : ℤ) ≤ score r s := by
  let ab : {x : ℕ × ℕ // HasRating x.1 x.2 r s} := ⟨(a, b), h⟩
  have hb : BddAbove (Set.range (fun ab : {x : ℕ × ℕ // HasRating x.1 x.2 r s} ↦
      ((ab : ℕ × ℕ).1 : ℤ) - ((ab : ℕ × ℕ).2 : ℤ))) := by
    refine ⟨n - 1, ?_⟩
    simp only [mem_upperBounds, Set.mem_range, Subtype.exists, exists_prop, Prod.exists,
               forall_exists_index, and_imp]
    rintro z a b hab rfl
    exact hab.sub_le
  exact le_ciSup hb ab

lemma hasRating_n_n {n : ℕ} (hn : 0 < n) (r : Fin n → Equiv.Perm (Fin n)) (s : Fin n) :
    HasRating n n r s := by
  refine ⟨hn, hn, Eq.le ?_⟩
  convert (Finset.card_univ (α := Fin n)).symm <;> simp

lemma score_le_of_forall_hasRating_le {n : ℕ} (hn : 0 < n) {m : ℤ}
    {r : Fin n → Equiv.Perm (Fin n)} {s : Fin n}
    (h : ∀ a b, HasRating a b r s → (a : ℤ) - (b : ℤ) ≤ m) : score r s ≤ m := by
  have : Nonempty ({x : ℕ × ℕ // HasRating x.1 x.2 r s}) := ⟨⟨(n, n), hasRating_n_n hn r s⟩⟩
  have hle : ∀ ab : {x : ℕ × ℕ // HasRating x.1 x.2 r s},
      ((ab : ℕ × ℕ).1 : ℤ) - ((ab : ℕ × ℕ).2 : ℤ) ≤ m := fun ab ↦ h _ _ ab.property
  exact ciSup_le hle

lemma score_eq_of_hasRating_of_forall_hasRating_le {n a b : ℕ} (hn : 0 < n)
    {r : Fin n → Equiv.Perm (Fin n)} {s : Fin n} (h : HasRating a b r s)
    (hle : ∀ a' b', HasRating a' b' r s → (a' : ℤ) - (b' : ℤ) ≤ (a : ℤ) - (b : ℤ)) :
    score r s = (a : ℤ) - (b : ℤ) :=
  le_antisymm (score_le_of_forall_hasRating_le hn hle) h.le_score

lemma hasRating_const {n a b : ℕ} {r : Equiv.Perm (Fin n)} {s : Fin n} :
    HasRating a b (Function.const _ r) s ↔ 0 < a ∧ a ≤ n ∧ (r s : ℕ) < b := by
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · rcases h with ⟨ha, -, h⟩
    refine ⟨ha, h.trans ?_, ?_⟩
    · convert Finset.card_filter_le _ _
      simp
    · by_contra hnlt
      simp [hnlt] at h
      omega
  · exact ⟨h.1, by omega, by simp [h.2.1, h.2.2]⟩

lemma score_const {n : ℕ} (hn : 0 < n) (r : Equiv.Perm (Fin n)) (s : Fin n) :
    score (Function.const _ r) s = n - (1 + (r s : ℕ)) := by
  convert score_eq_of_hasRating_of_forall_hasRating_le hn ?_ ?_
  · rw [hasRating_const]
    simp [hn]
  · simp_rw [hasRating_const]
    omega

lemma sum_score_const {n : ℕ} (hn : 0 < n) (r : Equiv.Perm (Fin n)) :
    ∑ s, score (Function.const _ r) s = n * (n - 1) / 2 := by
  refine Int.eq_ediv_of_mul_eq_right (by norm_num : (2 : ℤ) ≠ 0) ?_
  simp_rw [score_const hn, Finset.sum_sub_distrib, Finset.sum_add_distrib]
  have h := r.sum_comp Finset.univ (fun x ↦ ((x : ℕ) : ℤ))
    (Finset.coe_univ (α := Fin n) ▸ Set.subset_univ _)
  rw [h, ← Finset.sum_range, ← Nat.cast_sum (Finset.range n), mul_comm, sub_mul, add_mul,
      (by norm_num : (2 : ℤ) = (2 : ℕ)), ← Nat.cast_mul, Finset.sum_range_id_mul_two]
  push_cast
  rw [(by omega : ((n - 1) : ℕ) = ((n - 1) : ℤ))]
  simp
  ring

lemma score_mul_n_le_sum_weight {n : ℕ} (hn : 0 < n) (r : Fin n → Equiv.Perm (Fin n))
    (s : Fin n) : score r s * n ≤ ∑ i, (n - 1 - (r i s : ℕ) : ℤ) := by
  have h : ∀ a b, HasRating a b r s → ((a : ℤ) - (b : ℤ)) * n ≤ ∑ i, (n - 1 - (r i s : ℕ) : ℤ) := by
    intro a b h
    have han : a ≤ n := h.a_le_n
    by_cases hb : b ≤ n
    · rcases h with ⟨-, hb, h⟩
      calc ((a : ℤ) - (b : ℤ)) * n = a * n - b * n := by ring
        _ ≤ a * n - b * a := by gcongr
        _ = a * (n - b) := by ring
        _ ≤ ((Finset.univ : Finset (Fin n)).filter (fun i ↦ (r i s : ℕ) < b)).card * (n - b) := by
          gcongr
          omega
        _ = ∑ _ ∈ ((Finset.univ : Finset (Fin n)).filter (fun i ↦ (r i s : ℕ) < b)),
              (n - b : ℤ) := by simp [mul_sub]
        _ ≤ ∑ i ∈ ((Finset.univ : Finset (Fin n)).filter (fun i ↦ (r i s : ℕ) < b)),
              (n - 1 - (r i s : ℕ) : ℤ) := by
          simp_rw [sub_sub]
          gcongr with i hi
          rw [Finset.mem_filter] at hi
          omega
        _ ≤ ∑ i, (n - 1 - (r i s : ℕ) : ℤ) := Finset.sum_le_univ_sum_of_nonneg (by omega)
    · calc ((a : ℤ) - (b : ℤ)) * n ≤ 0 := by rw [mul_nonpos_iff]; omega
        _ ≤ ∑ i, (n - 1 - (r i s : ℕ) : ℤ) := Finset.sum_nonneg (by omega)
  rw [← Int.le_ediv_iff_mul_le (mod_cast hn)]
  refine score_le_of_forall_hasRating_le hn (fun a b hab ↦ ?_)
  rw [Int.le_ediv_iff_mul_le (mod_cast hn)]
  exact h a b hab

lemma sum_score_mul_n_le {n : ℕ} (hn : 0 < n) (r : Fin n → Equiv.Perm (Fin n)) :
    (∑ s, score r s) * n ≤ n * (n * (n - 1) / 2) :=
  calc (∑ s, score r s) * n = ∑ s, score r s * n := by rw [Finset.sum_mul]
    _ ≤ ∑ s, ∑ i, (n - 1 - (r i s : ℕ) : ℤ) := by gcongr; exact score_mul_n_le_sum_weight hn _ _
    _ = ∑ i, ∑ s, (n - 1 - (r i s : ℕ) : ℤ) := Finset.sum_comm
    _ = ∑ i : Fin n, (n * (n - 1) / 2 : ℤ) := by
      congr with i
      simp_rw [Finset.sum_sub_distrib]
      have h := (r i).sum_comp Finset.univ (fun x ↦ ((x : ℕ) : ℤ))
        (Finset.coe_univ (α := Fin n) ▸ Set.subset_univ _)
      rw [h, ← Finset.sum_range, ← Nat.cast_sum (Finset.range n)]
      refine Int.eq_ediv_of_mul_eq_right (by norm_num : (2 : ℤ) ≠ 0) ?_
      simp_rw [mul_sub, mul_comm (2 : ℤ)]
      rw [(by norm_num : (2 : ℤ) = (2 : ℕ)), ← Nat.cast_mul, Finset.sum_range_id_mul_two]
      push_cast
      rw [(by omega: ((n - 1) : ℕ) = ((n - 1) : ℤ))]
      simp
      ring
    _ = n * (n * (n - 1) / 2) := by simp

lemma sum_score_le {n : ℕ} (hn : 0 < n) (r : Fin n → Equiv.Perm (Fin n)) :
    (∑ s, score r s) ≤ (n * (n - 1) / 2) := by
  have h := sum_score_mul_n_le hn r
  rw [mul_comm] at h
  simpa [hn] using h

-- This is to be determined by the solver of the original problem.
def answer (n : ℕ) : ℤ := n * (n - 1) / 2

theorem result {n : ℕ} (hn : 0 < n) :
    (∀ r : Fin n → Equiv.Perm (Fin n), ∑ s, score r s ≤ answer n) ∧
    ∃ r : Fin n → Equiv.Perm (Fin n), ∑ s, score r s = answer n :=
  ⟨fun r ↦ sum_score_le hn r, Function.const _ (Equiv.refl _), sum_score_const hn _⟩

end IMOSL2024C1
