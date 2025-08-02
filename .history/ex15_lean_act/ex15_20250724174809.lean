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
variable (a : Fin k → ℕ)       -- a 是从 Fin k 到自然数的映射
variable (ha_inj : Function.Injective a)  -- a 的值互不相同
variable (ha_range : ∀ i, a i ∈ Set.Icc (1 : ℕ) n)  -- a 的值在 [1, n] 中
variable (hk1 : 1 ≤ k := Nat.le_trans (by decide) hk) -- 证明 1 <= k,用于 构造 a 0 => a ⟨0, hk1⟩

-- 辅助函数：将 Fin (k - 1) 的索引合法提升到 Fin k 中
-- 便于 处理,避免后文中每一次都重新计算 k - 1 的索引
def liftCastSucc {k : ℕ} (hk : 1 ≤ k) : Fin (k - 1) → Fin k :=
  fun i ↦ Fin.cast (by rw [Nat.sub_add_cancel hk]) i.castSucc

def liftSucc {k : ℕ} (hk : 1 ≤ k) : Fin (k - 1) → Fin k :=
  fun i ↦ Fin.cast (by rw [Nat.sub_add_cancel hk]) i.succ

def firstElement := a ⟨0, hk1⟩

-- 定义辅助引理
-- 根据条件 n |ai(ai+1 −1)，我们有：p |ai 且 q |ai+1 −1，其中 i = 1, . . . , k −1
-- 若 n = p * q 且 gcd(p, q) = 1，且 n ∣ x*y，则 p ∣ x ∧ q ∣ y
lemma coprime_mul_dvd
  (n p q x y : ℕ)
  (hnpq : n = p * q)
  (hpq_cop : Nat.Coprime p q)
  (hn_div : n ∣ x * y) :
  ∃ (x1 x2 : ℕ), p ∣ x1 ∧ q ∣ x2 ∧ x * y = x1 * x2 := sorry

lemma coprime_mul_dvd2
  (n p q x y : ℕ)
  (hnpq : n = p * q)
  (hpq_cop : Nat.Coprime p q)
  (hn_div : n ∣ x * y) :
  ∃ (x1 x2 : ℕ), p ∣ x1 ∧ q ∣ x2 ∧ x * y = x1 * x2 := by
    -- 因为 p 和 q 互质，所以我们可以利用中国剩余定理的思路
    -- 先从 n = p * q 和 n | x * y 推导出一些结论
    obtain ⟨k, hk⟩ := hn_div,  -- 从 n | x * y 推出 x * y = n * k
    have h1 : x * y = p * q * k := by rw [hnpq, hk]  -- 用 n = p * q 代入 x * y = n * k

    -- 接下来我们需要拆解 x * y = p * q * k，分别找到 x1 和 x2
    -- 由于 p 和 q 互质，可以应用互质的分解性质，使用欧几里得算法或者直接求解

    -- 我们通过欧几里得算法来分解 x * y，可以得到
    let x1 := p * (x * y / p)  -- 使得 x1 = p * (x * y / p)，必定有 p | x1
    let x2 := q * (x * y / q)  -- 使得 x2 = q * (x * y / q)，必定有 q | x2

    -- 验证 x1 和 x2 符合条件
    have h2 : p ∣ x1 := by { use (x * y / p), exact Nat.dvd_mul_left _ _ }
    have h3 : q ∣ x2 := by { use (x * y / q), exact Nat.dvd_mul_left _ _ }

    -- 最后，我们验证 x * y = x1 * x2
    have h4 : x * y = x1 * x2 := by { rw [x1, x2]; simp [h1] }

    -- 因此，x1 和 x2 满足条件
    use [x1, x2]
    split
    exact h2
    split
    exact h3
    exact h4



lemma lemma_1
  (hk1 : 1 ≤ k := Nat.le_trans (by decide) hk)
  (hdiv : ∀ i : Fin (k - 1), n ∣ a (liftCastSucc hk1 i) * (a (liftSucc hk1 i) - 1)) :
  ∃ p q, p ∣ a ⟨0, hk1⟩ ∧ q ∣ a ⟨1, hk⟩  - 1 ∧ gcd p q = 1 := by
  -- 使用题设条件，获取 p 和 q
  let p := gcd n (a ⟨0, hk1⟩)
  let q := gcd n (a ⟨1, hk⟩ - 1)

  -- 证明 p ∣ a 0 且 q ∣ a 1 - 1
  have hp : p ∣ a ⟨0, hk1⟩ := gcd_dvd_right _ _
  have hq : q ∣ a ⟨1, hk⟩ - 1 := gcd_dvd_right _ _

  -- -- 证明 gcd(p, q) = 1
  -- have h_gcd : gcd p q = 1 := by
  --   apply Nat.coprime_iff_gcd_eq_one.mpr
  --   intro  hk_prime hk_p
  --   -- 假设 k 是 p 的素数因子，证明 k 不是 q 的因子
  --   have hk_q : ¬ k ∣ q := by
  --     intro hk_q
  --     -- 如果 k ∣ q，则 k 同时整除 p 和 q，与 gcd(p, q) = 1 矛盾
  --     have hk_gcd : k ∣ gcd p q := Nat.dvd_gcd hk_p hk_q
  --     rw [h_gcd] at hk_gcd
  --     exact Nat.Prime.not_dvd_one hk_prime hk_gcd
  --   exact hk_q

  -- 证明 gcd(p, q) = 1
  have h_gcd : gcd p q = 1 := by
    apply Nat.coprime_iff_gcd_eq_one.mpr
    -- 构造匿名函数，直接处理目标
    exact fun k hk_prime hk_p =>
      -- 假设 k 是 p 的素数因子，证明 k 不是 q 的因子
      have hk_q : ¬ k ∣ q := fun hk_q =>
        -- 如果 k ∣ q，则 k 同时整除 p 和 q，与 gcd(p, q) = 1 矛盾
        have hk_gcd : k ∣ gcd p q := Nat.dvd_gcd hk_p hk_q
        -- 利用 gcd p q = 1，将 k ∣ gcd p q 转化为 k ∣ 1
        -- 由于 k 是素数，k 不可能整除 1
        Nat.Prime.not_dvd_one hk_prime hk_gcd
      hk_q

  -- 构造两个互质的因子 p 和 q
  exact ⟨p, q, hp, hq, h_gcd⟩

-- 根据条件 n | ai * (a_{i+1} - 1)，推导出 p ∣ a_i 且 q ∣ a_{i+1} - 1
lemma lemma_2
  (i : Fin (k - 1)) :
  p n a i ∣ a i ∧ q n a i ∣ a (i + 1) - 1 := by
  -- 定义 p 和 q
  let p := gcd n (a i)
  let q := gcd n (a (i + 1) - 1)

  -- 根据 gcd 的性质，p ∣ a_i 且 q ∣ a_{i+1} - 1
  have hp : p ∣ a i := gcd_dvd_right n (a i)
  have hq : q ∣ a (i + 1) - 1 := gcd_dvd_right n (a (i + 1) - 1)

  -- 返回结果
  exact ⟨hp, hq⟩
/--
设 `n` 为正整数，`k ≥ 2`。
`a : Fin k → ℕ` 满足：
1. `a` 单射；
2. `1 ≤ a i ≤ n`；
3. ∀ i ∈ Fin (k - 1)，有 `n ∣ a i * (a (i + 1) - 1)` 成立。

则 `n` 不整除 `a_{k - 1} * (a_0 - 1)`。
-/
theorem number_theory_68849
  (hk1 : 1 ≤ k := Nat.le_trans (by decide) hk)
  (hdiv : ∀ i : Fin (k - 1), n ∣ a (liftCastSucc hk1 i) * (a (liftSucc hk1 i) - 1)) :
  ¬ n ∣
    a ⟨k - 1, Nat.sub_lt (lt_of_lt_of_le (by decide) hk) (by decide)⟩ *
    (a ⟨0, Nat.lt_of_lt_of_le (by decide) hk⟩ - 1) := sorry

end NumberTheory
