import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.NumberTheory.Divisors

open Nat

namespace NumberTheory

-- 定义命名空间下全局变量和假设
variable (n : ℕ) (hn : 1 < n)  -- n 是正整数
variable (k : ℕ) (hk : 1 ≤ k)  -- k 是大于等于 2 的自然数 , 用于构造 a 1 => a⟨1, hk⟩
variable (a : Fin k → ℕ)      -- a 是从 Fin k 到自然数的映射
-- a 的性质,互异性以及范围
variable (ha_inj : Function.Injective a)  -- a 的值互不相同
variable (ha_range : ∀ i, a i ∈ Set.Icc (1 : ℕ) n)  -- a 的值在 [1, n] 中

-- 引申条件 以及 方便的假设
variable (hk0 : 0 < k := Nat.lt_of_lt_of_le (by decide) hk)
-- variable (hk1 : 1 < k := Nat.lt_of_lt_of_le (by decide) hk) -- 证明 1 <= k,用于 构造 a 0 => a ⟨0, hk1⟩
variable (i : Fin (k - 1)) (h0i : 0 < i.val)-- i 是 Fin k 中的一个元素,便于后续使用 a i


-- 辅助函数：将 Fin (k - 1) 的索引合法提升到 Fin k 中
-- 便于 处理,避免后文中每一次都重新计算 k - 1 的索引
def liftCastSucc {k : ℕ} (hk : 1 ≤ k) : Fin (k - 1) → Fin k :=
  fun i ↦ Fin.cast (by rw [Nat.sub_add_cancel hk]) i.castSucc

def liftSucc {k : ℕ} (hk : 1 ≤ k) : Fin (k - 1) → Fin k :=
  fun i ↦ Fin.cast (by rw [Nat.sub_add_cancel hk]) i.succ

-- 简写 a_0,a_i
def a_0 := a ⟨0, hk0⟩ -- 后续使用a₀
-- def a_1 := a ⟨1, hk1⟩ -- 后续使用a₁
def a_i := a (liftCastSucc hk0 i) -- aᵢ
def a_i_succ := a (liftSucc hk0 i) -- aᵢ₊₁


-- 验证
#check a
#check i
#check a_i
#check a ⟨0, hk0⟩  -- a ⟨1, hk1⟩ 是一个自然数



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
  (hk1 : 1 ≤ k := Nat.le_trans (by decide) hk)
  (hdiv : ∀ i : Fin (k - 1), n ∣ a (liftCastSucc hk0 i) * (a (liftSucc hk0 i) - 1)) :
  -- -- 之所以不在此处将 a (liftSucc hk0 i) 等同 a_i_succ, 是因为 lean 推断不出来类型,以及后续需要使用 a_i_succ 的定义
  ¬ n ∣
    a ⟨k - 1, Nat.sub_lt (lt_of_lt_of_le (by decide) hk) (by decide)⟩ *
    (a ⟨0, Nat.lt_of_lt_of_le (by decide) hk⟩ - 1) := sorry


/--Lemma `step1`: Let $n>1$ and suppose $n\mid a_0(a_1-1)$.  Setting
$p = \gcd(n,a_0)$ and $q = n/p$, we have $p\mid a_0$, $q\mid (a_1-1)$, and $\gcd(q,a_1)=1$.
-/

lemma step1 {n a0 a1 : ℕ} (hn : n > 1) (hdiv : n ∣ a0 * (a1 - 1)) :
  (Nat.gcd n a0 ∣ a0) ∧ ((n / Nat.gcd n a0) ∣ (a1 - 1)) ∧ Nat.gcd (n / Nat.gcd n a0) a1 = 1 :=
  let p := Nat.gcd n a0  -- 定义 p
  let q := n / p         -- 定义 q
  -- proof p ∣ a0
  have h_p_dvd : p ∣ a0 := Nat.gcd_dvd_right n a0
  -- proof : n = p * q
  have h_n_eq : n = p * q := Nat.mul_div_cancel' (Nat.gcd_dvd_left n a0)
  have h_p_div_n_a0 : Nat.gcd n a0 = p := rfl
  have h_n_dvd_mul : n ∣ a0 * (a1 - 1) := hdiv
  -- proof : q ∣ (a1 - 1)
  have h_q_dvd : q ∣ (a1 - 1) := by
    rw h_n_dvd_mul at h_n_eq






lemma step1_try {n a0 a1 : ℕ} (hn : n > 1) (hdiv : n ∣ a0 * (a1 - 1)) :
  (Nat.gcd n a0 ∣ a0) ∧ ((n / Nat.gcd n a0) ∣ (a1 - 1)) ∧ Nat.gcd (n / Nat.gcd n a0) a1 = 1 :=
  let p := Nat.gcd n a0
  let q := n / p
  have h_p_dvd : p ∣ a0 := Nat.gcd_dvd_right n a0
  have h_n_eq : n = p * q := Nat.mul_div_cancel' (Nat.gcd_dvd_left n a0)
  have h_p_div_n_a0 : Nat.gcd n a0 = p := rfl
  have h_n_dvd_mul : n ∣ a0 * (a1 - 1) := hdiv
  have h_pq_dvd_mul : p * q ∣ a0 * (a1 - 1) := by simp [h_n_eq, h_n_dvd_mul]
  have h_a0_eq_p_k : ∃ k, a0 = p * k := Nat.dvd_iff_exists_eq_mul_left.mp h_p_dvd
  let ⟨k, hk⟩ := h_a0_eq_p_k
  have h_pq_dvd_pk_mul : p * q ∣ (p * k) * (a1 - 1) := by simp [hk, h_pq_dvd_mul]
  have h_q_dvd_k_mul : q ∣ k * (a1 - 1) := by
    apply (Nat.mul_dvd_mul_left p).mp at h_pq_dvd_pk_mul
    exact h_pq_dvd_pk_mul
  have h_gcd_q_k_eq_one : Nat.gcd q k = 1 := by
    rw [← Nat.gcd_mul_left p, hk, h_n_eq, h_p_div_n_a0]
    exact Nat.gcd_div_dvd_left _ _
  have h_q_dvd_a1_sub_1 : q ∣ (a1 - 1) := Nat.dvd_of_gcd_eq_one_left_of_dvd h_gcd_q_k_eq_one h_q_dvd_k_mul
  sorry

/--
Lemma `step2`: Propagation step.  If $q\mid n$, $n>1$, and $n\mid a\cdot(b-1)$,
and moreover $\gcd(q,a)=1$, then $q\mid (b-1)$ and $\gcd(q,b)=1$.
-/
lemma step2 {q a b n : ℕ} (hq_n : q ∣ n) (hdiv : n ∣ a * (b - 1)) (hg : Nat.gcd q a = 1) :
  (q ∣ (b - 1)) ∧ (Nat.gcd q b = 1) :=
  -- Since q | n and n | a*(b-1), we have q | a*(b-1):
  have h_q_div_prod : q ∣ a * (b - 1) := Nat.dvd_trans hq_n hdiv
  -- Write q | a*(b-1) as a*(b-1) = q * k
  rcases h_q_div_prod with ⟨k, hk⟩
  -- Compute gcd(q, a*(b-1)).  Since gcd(q,a)=1,
  -- Nat.gcd_mul_left q 1 k gives gcd(q, q*k) = q.
  have h_gcd_q_prod : Nat.gcd q (a * (b - 1)) = q
  { rw [hk, Nat.gcd_mul_left q 1 k], exact Nat.gcd_one_left q }
  -- Also gcd(q, a*(b-1)) = gcd(q, b-1) by gcd_mul_right_right_of_gcd_eq_one,
  have h_gcd_b1 : Nat.gcd q (b - 1) = q :=
    Nat.gcd_mul_right_right_of_gcd_eq_one hg ▸ h_gcd_q_prod
  -- From gcd(q, b-1) = q we know q | (b-1) (gcd divides its arguments).
  have h_q_b1 : q ∣ (b - 1) := Nat.gcd_dvd_right q (b - 1) h_gcd_b1
  -- Finally, b = (b-1)+1 ≡ 1 mod q, so gcd(q,b)=1:
  have h_gcd_q_b : Nat.gcd q b = 1
  { rw [Nat.gcd_comm, Nat.gcd_mul_right_add_left (b - 1) 1 q]
    simp [h_gcd_b1] }
  exact ⟨h_q_b1, h_gcd_q_b⟩

/--
Main Theorem: Let $n>1$ and $a_0,a_1,\dots,a_k$ ($k\ge1$) be distinct integers in $\{1,\dots,n\}$
with $n\mid a_i(a_{i+1}-1)$ for $i=0,\dots,k-1$.  Then $n\nmid a_k(a_0-1)$.
-/
theorem ex15_main (n a0 a1 ak : ℕ) (hk : 1 ≤ k)
  (hdist : a0 ≠ ak) -- we only need a0 ≠ ak from distinctness
  (h01 : n ∣ a0 * (a1 - 1))
  (hchain : ∀ i, 1 ≤ i ∧ i < k → n ∣ ( (if i=1 then a1 else if i=0 then a0 else 0) *
                                      (if i+1=0 then a0 else if i+1=1 then a1 else ak) - 1)) :
  ¬ (n ∣ (ak * (a0 - 1))) :=
  -- Apply step1 to the initial divisibility a0*(a1-1):
  let p := Nat.gcd n a0
  let q := n / p
  have step₁ := step1 (by linarith) h01
  obtain ⟨h_p_dvd, h_q_dvd, h_gcd1⟩ := step₁,
  -- From h_q_dvd and gcd(q,a1)=1, propagate along the chain:
  have h_q_div_all : q ∣ (ak - 1) ∧ Nat.gcd q ak = 1,
  { -- Start with i=1 case: q|(a1-1) and gcd(q,a1)=1
    have h_q_a1_1 := ⟨h_q_dvd, h_gcd1⟩,
    -- Iterate Lemma step2 to reach ak:
    induction k with k ih generalizing a1 ak,
    { exact h_q_a1_1 }, -- trivial for k=1
    { -- Assume for a_i, prove for a_{i+1}
      -- (In a full proof, we would use the chain condition. Here, sketching.)
      admit } },
  -- From the propagation, we get q | (ak-1).
  cases h_q_div_all with h_q_ak1 h_gcd_k,
  -- Now p|a0 and q|(ak-1) imply n=p*q divides a0*(ak-1):
  have h_n_div := Nat.mul_dvd_mul h_p_dvd h_q_ak1,
  -- Argue by contradiction: assume n | ak*(a0-1):
  intro h_contr,
  -- Then n | a0*(ak-1) and n | ak*(a0-1), so n divides their difference:
  have h_diff : n ∣ (ak - a0),
  { rw [mul_sub, mul_sub, sub_sub_cancel] at h_n_div h_contr,
    exact Nat.dvd_sub h_n_div h_contr },
  -- But 0 < |ak - a0| < n since a0,ak ∈ {1..n} and distinct, so impossible:
  have h_nonzero : ak ≠ a0 := hdist,
  have h_bounds : |(ak : ℤ) - (a0 : ℤ)| < (n : ℤ) := by sorry,
  -- Contradiction: a nonzero integer of absolute value < n cannot be divisible by n>1.
  exact absurd h_nonzero (by { lift 0 < a0 < n with ha0,
                               lift 0 < ak < n with hak,
                               simp only [Int.coe_nat_lt, Int.coe_nat_zero] at *,
                               linarith })


end NumberTheory
