/-
Copyright (c) 2024 Joseph Myers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Myers
-/
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Normed.Ring.Lemmas
import Mathlib.Data.Int.Star
import Mathlib.Data.Nat.Log

namespace IMOSL2024A2

-- Following Solution 2.

def xmap (n : ℕ) : ℕ ↪ ℕ where
  toFun := fun m ↦ 2 ^ n * (2 * m + 1)
  inj' := fun x y h ↦ by
    dsimp only at h
    rwa [Nat.mul_right_inj (by simp), add_left_inj, Nat.mul_right_inj (by simp)] at h

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
      have h_exp : ∀ m k : ℕ, 2^i.val * (2 * m + 1) ≠ 2^j.val * (2 * k + 1) := by
        intro m k h_eq
        by_cases h_cases : i.val < j.val
        · have h_div : 2 ^ (j.val - i.val) * (2 * k + 1) = 2 * m + 1 := by
            refine mul_left_cancel₀ (pow_ne_zero i two_ne_zero) ?_
            rw [← mul_assoc, ← pow_add, Nat.add_sub_of_le h_cases.le, h_eq]
          replace h_div := congr_arg Even h_div
          simp_all only [Finset.mem_coe, ne_eq, Fin.val_fin_lt, Nat.even_mul, Nat.even_pow,
            even_two, true_and, Nat.not_even_bit1, or_false, eq_iff_iff, iff_false,
            Decidable.not_not]
          exact absurd h_div (Nat.sub_ne_zero_of_lt h_cases)
        · obtain ⟨d, hd⟩ : ∃ d : ℕ, i.val = j.val + d ∧ 0 < d := by
            use i.val - j.val
            simp_all only [Finset.mem_coe, ne_eq, Fin.val_fin_lt, not_lt, Fin.val_fin_le,
              add_tsub_cancel_of_le, tsub_pos_iff_lt, true_and]
            exact lt_of_le_of_ne h_cases <| Ne.symm hij
          simp_all only [Finset.mem_coe, ne_eq, pow_add, mul_assoc, mul_eq_mul_left_iff,
            Nat.pow_eq_zero, OfNat.ofNat_ne_zero, Fin.val_eq_zero_iff, false_and, or_false,
            add_lt_iff_neg_left, not_lt_zero', not_false_eq_true]
          have := congr_arg Even h_eq
          simp [hd.2.ne', parity_simps] at this
      ext
      simp_all only [Finset.mem_coe, ne_eq, Finset.mem_inter, Finset.mem_map, Finset.mem_range,
        Finset.notMem_empty, iff_false, not_and, not_exists, forall_exists_index, and_imp]
      exact fun x_3 a_1 a_2 x_4 a_3 ↦ ne_of_ne_of_eq (fun a ↦ h_exp x_3 x_4 a.symm) a_2
    _ ⊆ ∅ := Finset.Subset.refl _

lemma card_x_to_finset {n : ℕ} (x : Fin (n + 1) → ℕ) : (x_to_finset x).card = ∑ i, x i := by
  have h_card_union : ∀ s : Finset (Fin (n + 1)),
      (Finset.biUnion s (fun i ↦ (Finset.range (x i)).map (xmap i))).card
          = ∑ i ∈ s, (Finset.range (x i)).card := by
    simp_all [disjoint_xmap, Finset.card_biUnion]
  simpa using h_card_union Finset.univ

lemma zero_not_mem_x_to_finset {n : ℕ} (x : Fin (n + 1) → ℕ) : 0 ∉ (x_to_finset x) := by
  simp only [x_to_finset, xmap, Finset.mem_biUnion, Finset.mem_univ, Finset.mem_map,
             Finset.mem_range, Function.Embedding.coeFn_mk, true_and, not_exists, not_and]
  intro i _ _
  positivity

lemma sum_two_pow_mul_sq {n : ℕ} (x : Fin (n + 1) → ℕ) :
    ∑ i : Fin (n + 1), 2 ^ (i : ℕ) * x i ^ 2 = ∑ i ∈ (x_to_finset x), i := by
  have h_sum :
      ∑ i ∈ x_to_finset x, i
          = ∑ i : Fin (n + 1), ∑ m ∈ Finset.range (x i), 2 ^ (i : ℕ) * (2 * m + 1) := by
    have h_disjoint :
        ∀ i j : Fin (n + 1), i ≠ j →
            Disjoint (Finset.image (fun m ↦ 2 ^ (i : ℕ) * (2 * m + 1)) (Finset.range (x i)))
                (Finset.image (fun m ↦ 2 ^ (j : ℕ) * (2 * m + 1)) (Finset.range (x j))) := by
      intro i j hij
      by_cases h_cases : i < j
      · rw [Finset.disjoint_left]
        intro a a_1
        simp_all only [ne_eq, Finset.mem_image, Finset.mem_range, not_exists, not_and]
        intro x_1 a_2
        obtain ⟨w, h⟩ := a_1
        obtain ⟨left, right⟩ := h
        subst right
        apply Aesop.BuiltinRules.not_intro fun a ↦ ?_
        have h_div : 2 ^ (j - i : ℕ) * (2 * x_1 + 1) = 2 * w + 1 := by
          refine mul_left_cancel₀ ( pow_ne_zero ( i : ℕ ) two_ne_zero ) ?_
          rw [← mul_assoc, ← pow_add, Nat.add_sub_of_le (mod_cast h_cases.le)]
          exact a
        replace h_div := congr_arg Even h_div
        simp_all +decide only [Nat.even_mul, Nat.even_pow, ne_eq, true_and, Nat.not_even_bit1,
          or_false, eq_iff_iff, iff_false, Decidable.not_not]
        exact absurd h_div ( Nat.sub_ne_zero_of_lt h_cases )
      · rw [Finset.disjoint_left]
        intro a a_1
        simp_all only [ne_eq, not_lt, Finset.mem_image, Finset.mem_range, not_exists, not_and]
        intro x_1 a_2
        obtain ⟨w, h⟩ := a_1
        obtain ⟨left, right⟩ := h
        subst right
        apply Aesop.BuiltinRules.not_intro fun a ↦ ?_
        have h_even : Even (2 ^ (i - j : ℕ)) :=
          even_iff_two_dvd.mpr (dvd_pow_self _ (Nat.sub_ne_zero_of_lt (h_cases.lt_of_ne' hij)))
        have h_div : 2 * x_1 + 1 = 2 ^ (i - j : ℕ) * (2 * w + 1) := by
          refine mul_left_cancel₀ ( pow_ne_zero j two_ne_zero ) ?_
          rw [← mul_assoc, ← pow_add, add_tsub_cancel_of_le (mod_cast h_cases)]
          exact a
        replace h_div := congr_arg Even h_div ; simp_all +decide [ parity_simps ];
    have h_sum_eq :
        ∑ i ∈ Finset.biUnion Finset.univ (fun i ↦ Finset.image (fun m ↦ 2 ^ i.val * (2 * m + 1))
            (Finset.range (x i))), i = ∑ i : Fin (n + 1),
                ∑ m ∈ Finset.range (x i), 2 ^ i.val * (2 * m + 1) := by
      rw [Finset.sum_biUnion]
      · exact Finset.sum_congr rfl fun i hi ↦ Finset.sum_image <| by aesop;
      · exact fun i _ j _ hij ↦ h_disjoint i j hij;
    convert h_sum_eq using 1;
    congr! 1;
    unfold x_to_finset; aesop;
  have h_inner : ∀ i : Fin (n + 1), ∑ m ∈ Finset.range (x i), (2 * m + 1) = x i ^ 2 :=
    fun i ↦ Nat.recOn (x i) (by norm_num) fun n ih ↦ by rw [Finset.sum_range_succ]; linarith
  simp +decide only [ h_sum, ← h_inner, Finset.mul_sum _ _ _ ]

lemma le_sum_two_pow_mul_sq {n : ℕ} (x : Fin (n + 1) → ℕ) :
    (∑ i, x i) * ((∑ i, x i) + 1) / 2 ≤ ∑ i : Fin (n + 1), 2 ^ (i : ℕ) * x i ^ 2 := by
  rw [sum_two_pow_mul_sq, ← card_x_to_finset]
  have h_min_sum : ∀ k S, S.card = k → (∀ i ∈ S, 0 < i) → (∑ i ∈ S, i) ≥ k * (k + 1) / 2 := by
    intro k S hS h_pos
    induction' k with k ih generalizing S
    · simp
    · obtain ⟨m, hm⟩ : ∃ m ∈ S, ∀ i ∈ S, i ≤ m :=
        ⟨Finset.max' S (Finset.card_pos.mp (by linarith)),
          Finset.max'_mem _ _, fun i hi ↦ Finset.le_max' _ _ hi⟩
      set S' := S \ {m}
      have hS' : S'.card = k := by rw [ Finset.card_sdiff ] <;> simp_all
      have h_pos' : ∀ i ∈ S', 0 < i := by aesop
      have hm_ge : m ≥ k + 1 := by
        have := Finset.card_le_card
          (show S ⊆ Finset.Icc 1 m from fun i hi ↦ Finset.mem_Icc.mpr ⟨h_pos i hi, hm.2 i hi⟩)
        aesop
      rw [Finset.sum_eq_sum_diff_singleton_add hm.1]
      apply Nat.div_le_of_le_mul
      nlinarith [hm_ge, ih S' hS' h_pos', Nat.div_mul_cancel (show 2 ∣ k * (k + 1)
        from even_iff_two_dvd.mp <| by simp [mul_add, parity_simps])]
  refine h_min_sum _ _ rfl fun i hi ↦ Nat.pos_of_ne_zero ?_
  exact Aesop.BuiltinRules.not_intro fun hi0 ↦ absurd (hi0 ▸ hi) (zero_not_mem_x_to_finset x)

def optimal_x (n : ℕ) (i : Fin (n + 1)) : ℕ := (n + 2 ^ (i : ℕ)) / 2 ^ ((i : ℕ) + 1)

lemma optimal_x_to_finset {n : ℕ} : x_to_finset (optimal_x n) = Finset.Icc 1 n := by
  ext a
  rw [Finset.mem_Icc]
  have := zero_not_mem_x_to_finset (optimal_x n)
  refine ⟨fun ha ↦ ⟨by grind, ?_⟩, fun ha ↦ ?_⟩
  · obtain ⟨i, m, hm⟩ : ∃ i m, a = 2^i * (2*m + 1) ∧ m < (n + 2^i) / 2^(i+1) := by
      simp only [x_to_finset, Finset.mem_biUnion, Finset.mem_univ, Finset.mem_map, Finset.mem_range,
        true_and] at ha
      aesop
    rw [Nat.lt_iff_add_one_le, Nat.le_div_iff_mul_le] at hm <;> ring_nf at *
      <;> norm_num [pow_succ']
    nlinarith [Nat.zero_le m]
  · obtain ⟨left, right⟩ := ha
    obtain ⟨i, m, hi⟩ : ∃ i m : ℕ, a = 2 ^ i * (2 * m + 1) := by
      induction' a using Nat.strongRecOn with a ih;
      rcases Nat.even_or_odd' a with ⟨k, rfl | rfl⟩
      · exact Exists.elim (ih k (by linarith) (by linarith) (by linarith))
          fun i hi ↦ hi.elim fun m hm ↦ ⟨i + 1, m, by rw [hm]; ring⟩
      · exact ⟨0, k, by ring⟩
    have hm : m < (n + 2 ^ i) / 2 ^ (i + 1) := by
      rw [Nat.lt_iff_add_one_le, Nat.le_div_iff_mul_le] <;> ring_nf
        <;> nlinarith [pow_pos (zero_lt_two' ℕ ) i]
    simp_all only [x_to_finset, Finset.mem_biUnion, Finset.mem_univ, Finset.mem_map,
      Finset.mem_range, true_and]
    have h_log : i ≤ Nat.log 2 n := Nat.le_log_of_pow_le (by norm_num) (by nlinarith)
    exact ⟨⟨i, Nat.lt_succ_of_le (h_log.trans (Nat.log_le_self _ _ ))⟩, m, hm, by norm_num [xmap]⟩

lemma sum_optimal_x (n : ℕ) : ∑ i, optimal_x n i = n := by
  have h_sum : ∑ i ∈ Finset.range (n + 1), (n + 2 ^ i) / 2 ^ (i + 1) = n := by
    have h_sum_floor :
        ∀ n, ∑ i ∈ Finset.range (Nat.log 2 n + 1), (n + 2 ^ i) / 2 ^ (i + 1) = n := by
      intro n
      induction' n using Nat.strong_induction_on with n ih
      have h_split :
        ∑ i ∈ Finset.range (Nat.log 2 n + 1), (n + 2 ^ i) / 2 ^ (i + 1)
          = (n + 1) / 2 + ∑ i ∈ Finset.range (Nat.log 2 n), (n / 2 + 2 ^ i) / 2 ^ (i + 1) := by
        rw [ Finset.sum_range_succ' ] ; norm_num [ Nat.pow_succ', ← Nat.div_div_eq_div_mul ] ;
        norm_num [ add_comm, Nat.add_mul_div_left, Nat.div_div_eq_div_mul ];
      rcases n with (_ | _ | n) <;> simp_all +decide;
      have := ih ((n + 1 + 1) / 2) (Nat.div_lt_of_lt_mul <| by linarith)
      rw [Nat.log_div_base] at this
      rcases k : Nat.log 2 (n + 1 + 1) with (_ | k) <;> simp_all +arith
      omega
    have h_zero_terms :
        ∀ i ∈ Finset.Ico (Nat.log 2 n + 1) (n + 1), (n + 2 ^ i) / 2 ^ (i + 1) = 0 := by
      simp only [Finset.mem_Ico, Nat.div_eq_zero_iff, Nat.pow_eq_zero,
        OfNat.ofNat_ne_zero, ne_eq, Nat.add_eq_zero, one_ne_zero, and_false, not_false_eq_true,
        and_true, false_or, and_imp]
      intro i hi₁ hi₂
      rw [pow_succ']
      linarith [Nat.lt_pow_of_log_lt one_lt_two hi₁]
    have : Nat.log 2 n + 1 ≤ n + 1 := by linarith [Nat.log_le_self 2 n]
    rw [← Finset.sum_range_add_sum_Ico _ this, Finset.sum_congr rfl h_zero_terms]
    aesop
  have h_sum_fin :
      ∑ i : Fin (n + 1), (n + 2 ^ (i : ℕ)) / 2 ^ ((i : ℕ) + 1)
        = ∑ i ∈ Finset.range (n + 1), (n + 2 ^ i) / 2 ^ (i + 1) := by
    have h_sum_fin :
        ∑ i ∈ Finset.range (n + 1), (n + 2 ^ i) / 2 ^ (i + 1)
          = ∑ i ∈ Finset.image (fun i : Fin (n + 1) ↦ i.val) .univ, (n + 2 ^ i) / 2 ^ (i + 1) := by
      rw [Finset.range_eq_Ico]
      congr
      ext i
      simp_all only [Nat.Ico_zero_eq_range, Finset.mem_range, Finset.mem_image, Finset.mem_univ,
        true_and]
      exact ⟨fun a ↦ ⟨⟨i, a⟩, rfl⟩, fun ⟨w, h⟩ ↦ h ▸ w.isLt⟩
    rw [h_sum_fin, Finset.sum_image]
    exact fun a ha b hb hab ↦ Fin.eq_of_val_eq hab
  exact h_sum_fin.trans h_sum

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
