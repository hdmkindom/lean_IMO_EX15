import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.NumberTheory.Divisors

open Nat

namespace NumberTheory

-- 定义命名空间下全局变量和假设
variable (n : ℕ) (hn : 0 < n)  -- n 是正整数
variable (k : ℕ) (hk : 2 ≤ k)  -- k 是大于等于 2 的自然数 , 用于构造 a 1 => a⟨1, hk⟩
variable (a : Fin k → ℕ)      -- a 是从 Fin k 到自然数的映射
-- a 的性质,互异性以及范围
variable (ha_inj : Function.Injective a)  -- a 的值互不相同
variable (ha_range : ∀ i, a i ∈ Set.Icc (1 : ℕ) n)  -- a 的值在 [1, n] 中

-- 引申条件 以及 方便的假设
variable (hk0 : 0 < k := Nat.lt_of_lt_of_le (by decide) hk)
variable (hk1 : 1 < k := Nat.lt_of_lt_of_le (by decide) hk) -- 证明 1 <= k,用于 构造 a 0 => a ⟨0, hk1⟩
variable (i : Fin k) (h : 0 < i)-- i 是 Fin k 中的一个元素,便于后续使用 a i


-- 辅助函数：将 Fin (k - 1) 的索引合法提升到 Fin k 中
-- 便于 处理,避免后文中每一次都重新计算 k - 1 的索引
def liftCastSucc {k : ℕ} (hk : 1 ≤ k) : Fin (k - 1) → Fin k :=
  fun i ↦ Fin.cast (by rw [Nat.sub_add_cancel hk]) i.castSucc

def liftSucc {k : ℕ} (hk : 1 ≤ k) : Fin (k - 1) → Fin k :=
  fun i ↦ Fin.cast (by rw [Nat.sub_add_cancel hk]) i.succ

def a_0 := a ⟨0, hk0⟩ -- 后续使用a_0
def a_1 := a ⟨1, hk1⟩ -- 后续使用a_1
def a_i := a i



#check i
#check a i
#check a ⟨0, hk0⟩  -- a ⟨1, hk1⟩ 是一个自然数
#check a ⟨1, hk1⟩  -- a ⟨1, hk1⟩ 是一个自然数
#check a (i.pred)
#check a ⟨i-1,hk_i1⟩  -- a ⟨i - 1, hk_i1⟩ 是一个自然数


example (p q c : ℕ) : p * q * c = q * p * c := by
  rw [mul_comm p q]

/--
设 `n` 为正整数，`k ≥ 2`。
`a : Fin k → ℕ` 满足：
1. `a` 单射；
2. `1 ≤ a i ≤ n`；
3. ∀ i ∈ Fin (k - 1)，有 `n ∣ a i * (a (i + 1) - 1)` 成立。

则 `n` 不整除 `a_{k - 1} * (a_0 - 1)`。
-/
theorem number_theory_68849
  -- (hk1 : 1 ≤ k := Nat.le_trans (by decide) hk)
  (hdiv : ∀ i : Fin (k - 1), n ∣ a (liftCastSucc hk0 i) * (a (liftSucc hk0 i) - 1)) :
  ¬ n ∣
    a ⟨k - 1, Nat.sub_lt (lt_of_lt_of_le (by decide) hk) (by decide)⟩ *
    (a ⟨0, Nat.lt_of_lt_of_le (by decide) hk⟩ - 1) := sorry


end NumberTheory
