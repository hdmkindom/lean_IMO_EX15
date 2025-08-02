import Mathlib.Data.Nat.Prime.Basic  -- 质数相关
import Mathlib.Data.Nat.Basic  -- 自然数基础
import Mathlib.Data.Finset.Basic  -- 有限集
import Mathlib.Algebra.BigOperators.Fin  -- 有限序列求和等
import Mathlib.NumberTheory.Divisors  -- 整除相关
open Nat Finset

-- theorem number_theory_68849
--     (n : ℕ) (hn : 0 < n)
--     (k : ℕ) (hk : k ≥ 2)
--     (a : Fin k → ℕ)
--     (ha : ∀ i j : Fin k, i ≠ j → a i ≠ a j)
--     (ha1 : ∀ i : Fin k, a i ∈ Set.Icc 1 n)
--     (hdiv : ∀ i : Fin k, i + 1 < k → n ∣ a i * (a (i + 1) - 1)) :
--     ¬ t n ∣ a ?k - 1, by omega? * (a ?0, by omega? - 1) := sorry

theorem imo_problem
    (n : ℕ) (hn : 0 < n)  -- n 是正整数
    (k : ℕ) (hk : k ≥ 2)  -- k ≥ 2
    (a : Fin k → ℕ)  -- a 是从 Fin k 到自然数的映射
    (ha : ∀ i j : Fin k, i ≠ j → a i ≠ a j)  -- a 的值互不相同
    (ha1 : ∀ i : Fin k, a i ∈ Set.Icc 1 n)  -- a 的值在 {1, ..., n} 中
    (hdiv : ∀ i : Fin (k - 1), n ∣ a i * (a ⟨i + 1, Nat.lt_of_succ_lt hk⟩ - 1)) :
    ¬ (n ∣ a ⟨k - 1, Nat.pred_lt hk⟩ * (a ⟨0, hk⟩ - 1)) := sorry
