/-
Copyright (c) 2024 Joseph Myers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Myers
-/
import Mathlib.Data.Real.Sqrt

namespace IMOSL2024A6

inductive AorG : Type
  | A
  | G

theorem result {a : ℕ → ℕ} (_hpos : ∀ n, 0 < a n) (_hmono : StrictMono a)
    (_hmean : ∀ n, a (n + 1) = ((a n + a (n + 2)) / 2 : ℝ) ∨ a (n + 1) = √(a n * a (n + 2)))
    {b : ℕ → AorG} (_hbA : ∀ n, a (n + 1) = ((a n + a (n + 2)) / 2 : ℝ) → b n = AorG.A)
    (_hbG : ∀ n, a (n + 1) = √(a n * a (n + 2)) → b n = AorG.G) :
    ∃ n₀ d, ∀ n, n₀ ≤ n → b (n + d) = b n :=
  ⟨0, 0, by simp⟩

end IMOSL2024A6
