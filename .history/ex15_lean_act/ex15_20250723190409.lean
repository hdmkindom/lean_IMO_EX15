import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.NumberTheory.Divisors

open Nat Finset

namespace NumberTheory

/--
设 `n` 是正整数，`k ≥ 2`，`a : Fin k → ℕ` 是一个函数，满足以下条件：
1. `a` 的值互不相同；
2. 对所有 `i`，有 `1 ≤ a i ≤ n`；
3. 对所有 `i : Fin (k - 1)`，都有 `n ∣ a i * (a (i + 1) - 1)`。

则有：
`n ∤ a (k - 1) * (a 0 - 1)`
-/
theorem no_full_cycle_mod_div
    (n : ℕ) (hn : 0 < n)
    (k : ℕ) (hk : 2 ≤ k)
    (a : Fin k → ℕ)
    (ha_inj : Function.Injective a)
    (ha_range : ∀ i, a i ∈ Set.Icc 1 n)
    (hdiv : ∀ i : Fin (k - 1), n ∣ a (Fin.castSucc i) * (a (Fin.castSucc i + 1) - 1)) :
    ¬ n ∣ a ⟨k - 1, Nat.sub_lt (lt_of_lt_of_le (by decide) hk) (by decide)⟩ * (a ⟨0, by linarith [hk]⟩ - 1) :=
  sorry

end NumberTheory
