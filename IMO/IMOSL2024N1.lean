/-
Copyright (c) 2024 Joseph Myers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Myers
-/
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.NormNum.Prime

namespace IMOSL2024N1

def Condition (n : ℕ) : Prop := ∀ d, d ∣ n → d + 1 ∣ n ∨ (d + 1).Prime

-- Following Solution 1.

lemma condition_one : Condition 1 := by
  rw [Condition]
  intro d h
  have hle := Nat.le_of_dvd (by decide) h
  interval_cases d <;> decide

lemma condition_two : Condition 2 := by
  rw [Condition]
  intro d h
  have hle := Nat.le_of_dvd (by decide) h
  interval_cases d <;> decide

lemma condition_four : Condition 4 := by
  rw [Condition]
  intro d h
  have hle := Nat.le_of_dvd (by decide) h
  interval_cases d <;> decide

lemma condition_twelve : Condition 12 := by
  rw [Condition]
  intro d h
  have hle := Nat.le_of_dvd (by decide) h
  revert h
  interval_cases d <;> decide

lemma three_dvd_two_pow_odd_add_one {n : ℕ} (hn : Odd n) : 3 ∣ 2 ^ n + 1 := by
  rcases hn with ⟨k, rfl⟩
  rw [Nat.pow_add_one, pow_mul, Nat.dvd_iff_mod_eq_zero, Nat.add_mod, Nat.mul_mod, Nat.pow_mod]
  norm_num

namespace Condition

lemma add_one_dvd_of_dvd_not_prime {n d : ℕ} (hc : Condition n) (hd : d ∣ n)
    (hd1 : ¬(d + 1).Prime) : d + 1 ∣ n := (hc d hd).resolve_right hd1

lemma add_one_prime_of_dvd_not_dvd {n d : ℕ} (hc : Condition n) (hd : d ∣ n)
    (hd1 : ¬d + 1 ∣ n) : (d + 1).Prime := (hc d hd).resolve_left hd1

lemma le_two_of_pow_two {k : ℕ} (hc : Condition (2 ^ k)) : k ≤ 2 := by
  by_contra h
  rw [not_le, ← Nat.succ_le_iff] at h
  norm_num at h
  have h9 : 2 ^ 3 + 1 ∣ 2 ^ k := hc.add_one_dvd_of_dvd_not_prime (pow_dvd_pow _ h) (by norm_num)
  have h32 := Nat.prime_three.dvd_of_dvd_pow (Dvd.dvd.trans (by norm_num) h9)
  norm_num at h32

lemma add_one_eq_two_pow_of_two_pow_mul_odd {k m : ℕ} (hc : Condition (2 ^ k * m)) (hm : Odd m)
    (hm1 : 1 < m) :
    ∃ t, 2 ≤ t ∧ t ≤ k ∧ m + 1 = 2 ^ t := by
  by_cases h : (m + 1).Prime
  · rcases h.eq_two_or_odd' with ho | ho
    · omega
    · rw [← Nat.not_even_iff_odd] at ho
      exact False.elim (ho (hm.add_odd odd_one))
  · have hcm := hc.add_one_dvd_of_dvd_not_prime (dvd_mul_left _ _) h
    rw [Nat.Coprime.dvd_mul_right (by simp), Nat.dvd_prime_pow Nat.prime_two] at hcm
    rcases hcm with ⟨t, ht⟩
    refine ⟨t, ?_, ht⟩
    by_contra ht2
    interval_cases t <;> omega

lemma two_pow_add_one_prime {k m t : ℕ} (hc : Condition (2 ^ k * m)) (ht2 : 2 ≤ t) (htk : t ≤ k)
    (htm : m + 1 = 2 ^ t) : (2 ^ k + 1).Prime := by
  refine hc.add_one_prime_of_dvd_not_dvd (dvd_mul_right (2 ^ k) m) ?_
  rw [Nat.Coprime.dvd_mul_left (by simp)]
  refine Nat.not_dvd_of_pos_of_lt ?_ ?_
  · by_contra h
    simp only [not_lt, nonpos_iff_eq_zero] at h
    subst h
    rw [zero_add, eq_comm] at htm
    rw [pow_eq_one_iff_of_nonneg (by decide) (by omega)] at htm
    simp at htm
  · calc m < 2 ^ t := by omega
      _ ≤ 2 ^ k := pow_le_pow_right₀ (by norm_num) htk
      _ < 2 ^ k + 1 := by omega

lemma two_pow_sub_one_add_one_prime {k m t : ℕ} (hc : Condition (2 ^ k * m)) (ht2 : 2 ≤ t)
    (htk : t ≤ k) (htm : m + 1 = 2 ^ t) : (2 ^ (k - 1) + 1).Prime := by
  rw [← Nat.sub_add_cancel (n := k) (m := 1) (by omega), Nat.pow_add_one, mul_assoc] at hc
  by_cases hk2 : k = 2
  · subst hk2
    norm_num
  · refine hc.add_one_prime_of_dvd_not_dvd (dvd_mul_right (2 ^ (k - 1)) (2 * m)) ?_
    rw [Nat.Coprime.dvd_mul_left (by simp), Nat.Coprime.dvd_mul_left]
    · by_cases hk : k = t
      · subst hk
        have hp : 2 ^ k = 2 ^ (k - 1) * 2 := by
          rw [← Nat.pow_add_one]
          simp
          omega
        rw [hp] at htm
        intro h
        have h' : 2 ^ (k - 1) + 1 ∣ 2 * (2 ^ (k - 1) + 1) - m := by
          exact Nat.dvd_sub (dvd_mul_left _ _) h
        have h3 : 2 ^ (k - 1) + 1 ∣ 3 := by
          convert h'
          omega
        refine Nat.not_dvd_of_pos_of_lt (by norm_num) ?_ h3
        calc 3 = 2 ^ 1 + 1 := by norm_num
          _ < 2 ^ (k - 1) + 1 := by gcongr <;> omega
      · refine Nat.not_dvd_of_pos_of_lt ?_ ?_
        · by_contra h
          simp only [not_lt, nonpos_iff_eq_zero] at h
          subst h
          rw [zero_add, eq_comm] at htm
          rw [pow_eq_one_iff_of_nonneg (by decide) (by omega)] at htm
          simp at htm
        · calc m < 2 ^ t := by omega
            _ ≤ 2 ^ (k - 1) := pow_le_pow_right₀ (by norm_num) (by omega)
            _ < 2 ^ (k - 1) + 1 := by omega
    · suffices (2 * 2 ^ (k - 2) + 1).Coprime 2 by
        convert this using 2
        rw [← Nat.pow_add_one']
        congr
        omega
      simp

lemma eq_two_of_two_pow_mul {k m t : ℕ} (hc : Condition (2 ^ k * m)) (ht2 : 2 ≤ t) (htk : t ≤ k)
    (htm : m + 1 = 2 ^ t) : k = 2 := by
  have hp := hc.two_pow_add_one_prime ht2 htk htm
  have hp1 := hc.two_pow_sub_one_add_one_prime ht2 htk htm
  by_cases h : Even k
  · have h' : Odd (k - 1) := Nat.Even.sub_odd (by omega) h (by norm_num)
    have h3 : 3 ∣ 2 ^ (k - 1) + 1 := three_dvd_two_pow_odd_add_one h'
    rw [hp1.dvd_iff_eq (by norm_num), ← eq_tsub_iff_add_eq_of_le (by norm_num)] at h3
    norm_num at h3
    rw [Nat.pow_eq_self_iff (by norm_num)] at h3
    omega
  · rw [Nat.not_even_iff_odd] at h
    have h3 : 3 ∣ 2 ^ k + 1 := three_dvd_two_pow_odd_add_one h
    rw [hp.dvd_iff_eq (by norm_num), ← eq_tsub_iff_add_eq_of_le (by norm_num)] at h3
    norm_num at h3
    rw [Nat.pow_eq_self_iff (by norm_num)] at h3
    omega

lemma eq_one_or_two_or_four_or_twelve {n : ℕ} (hc : Condition n) (h : 0 < n) :
    n = 1 ∨ n = 2 ∨ n = 4 ∨ n = 12 := by
  rcases Nat.exists_eq_two_pow_mul_odd h.ne' with ⟨k, m, hm, rfl⟩
  by_cases hm1 : m = 1
  · subst hm1
    rw [mul_one] at hc
    have hk := hc.le_two_of_pow_two
    interval_cases k <;> norm_num
  · have hm1' : 1 < m := by
      by_contra hm1'
      interval_cases m <;> omega
    rcases hc.add_one_eq_two_pow_of_two_pow_mul_odd hm hm1' with ⟨t, ht2, htk, htm⟩
    have hk2 := hc.eq_two_of_two_pow_mul ht2 htk htm
    subst hk2
    have ht2 : t = 2 := le_antisymm htk ht2
    subst ht2
    omega

end Condition

-- This is to be determined by the solver of the original problem.
def solutionSet : Set ℕ := {1, 2, 4, 12}

theorem result {n : ℕ} (h : 0 < n) :
    Condition n ↔ n ∈ solutionSet := by
  refine ⟨fun hc ↦ ?_, fun hc ↦ ?_⟩
  · exact hc.eq_one_or_two_or_four_or_twelve h
  · simp_rw [solutionSet, Set.mem_insert_iff, Set.mem_singleton_iff] at hc
    rcases hc with rfl | rfl | rfl | rfl
    · exact condition_one
    · exact condition_two
    · exact condition_four
    · exact condition_twelve

end IMOSL2024N1
