import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.NumberTheory.Divisors
import Mathlib.Tactic
import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Data.Int.Basic
import Mathlib.Data.Fin.Basic

open Nat
open NumberTheorySymbols

namespace NumberTheory

-- 定义命名空间下全局变量和假设
def A (k : ℕ) : Set ℕ := {m| 1 ≤ m ∧ m ≤ k}
def B (n : ℕ) : Set ℕ := {w| 1 ≤ w ∧ w ≤ n}
def C (k : ℕ) : Set ℕ := {s| 1 ≤ s ∧ s ≤ k-1}
variable (n m w k s : ℕ)
variable (hn : 1 ≤ n) (hnk : k ≤ n)
variable (hm : 1 ≤ m ∧ m ≤ k) (hw : 1 ≤ w ∧ w ≤ n)
variable (hs : 1 ≤ s ∧ s ≤ k - 1) (hk : 2 ≤ k)
variable (a : ℕ → ℕ) (h_range : ∀ i, i ∈ A k → a i ∈ B n)
variable (i : ℕ)
variable (h_inj : ∀ n1 n2, n1 ∈ A k → n2 ∈ B n → a n1 = a n2 → n1 = n2)
variable (h_dvd : ∀ i, i ∈ C k → n ∣ (a i) * (a (i + 1) - 1))

-- 辅助引理1：如果 q | a - 1 且 q | a * b，则 q | b
lemma lemma1 {q a b : ℕ} (ha : 1 ≤ a) (h1 : q ∣ a - 1) (h2 : q ∣ a * b) : q ∣ b := by
  have h_coprime : Nat.gcd a q =1 := by
    set d := Nat.gcd a q
    have h_dvd_q: d ∣ q := Nat.gcd_dvd_right a q
    have h_dvd_a : d ∣ a := Nat.gcd_dvd_left a q
    have h_dvd_a1 : d ∣ a - 1 := Nat.dvd_trans  h_dvd_q h1
    have h_dvd_a3 : a-(a-1) = 1 := Nat.sub_sub_self (by linarith)
    have h_ : a-1 ≤ a := Nat.sub_le a 1
    have h_dvd_a2  : d ∣ a-(a-1) := by
      exact Nat.dvd_sub  h_dvd_a h_dvd_a1
    rw [h_dvd_a3] at h_dvd_a2
    have d_ : d=1 :=Nat.dvd_one.mp h_dvd_a2
    exact d_
  --由于下面引用的函数对互质条件里的a q 的顺序有要求，所以进行重写
  have h_coprime' : Nat.gcd q a =1 := Nat.gcd_comm a q ▸ h_coprime
  exact Coprime.dvd_of_dvd_mul_left h_coprime' h2

-----------------------------------------------------------------------
--证明{1..n}集合内不同数的差不可能被n整除
lemma lemma2 {n a b : ℤ} (ha : 1 ≤ a ∧ a ≤ n) (hb : 1 ≤ b ∧ b ≤ n)
    (he : b ≠ a) (hdvd : n ∣ b - a) : False := by
  have hsub : |(b - a :ℤ  )| < n := by
  --证明b-a的绝对值小于n
    rw [abs_lt]
    constructor <;> linarith
    --应用线性引理策略自动能够证明
  have hzero := Int.eq_zero_of_abs_lt_dvd hdvd hsub
  --引用定理证明a-b=0
  simp only [sub_eq_zero] at hzero
  exact he hzero
  --与假设a和b不相等矛盾

--------------------------------------------------------------------------------------
--证明n|a1*(a2-1) p=gcd(n,a1) q=n/p  则p|a1 且 q|(a2-1)

lemma lemma3 {n a1 a2 : ℕ} (ha1 : 1 ≤ a1 ∧ a1 ≤ n) (h : n ∣ a1 * (a2 - 1)) :
Nat.gcd n a1∣ a1 ∧ (n / Nat.gcd n a1) ∣ (a2 - 1) := by
  -- 设置p和q的定义
  set p := Nat.gcd n a1
  set q := n / p
  set m := a1 / p

  --证明 p ∣ a1
  have h_p_dvd_a1 : p ∣ a1 := by
    exact Nat.gcd_dvd_right n a1  -- 最大公约数的基本性质


  --证明 q ∣ (a₂ - 1)
  have h_q_dvd_a2_sub_one : q ∣ (a2 - 1) := by
    --n= p * q
    have h_n_eq : n = p*q :=by
      rw [Nat.mul_div_cancel' (Nat.gcd_dvd_left n a1)]
    -- 由于 p ∣ n 和 p ∣ a1，可以写出 n = p*q 和 a1 = p*m
    have h_a1_eq : a1 = p * m := by
      rw [Nat.mul_div_cancel' (Nat.gcd_dvd_right n a1)]

    -- 代入整除条件：n ∣ a1*(a2-1)
    rw [h_n_eq, h_a1_eq, mul_assoc] at h


    -- 证明 p > 0
    have hp_pos : p > 0 := gcd_pos_of_pos_right n  ha1.1

    -- p*q |p*(m*(a2-1))两边同除p  得到 q ∣ m*(a2-1)
    have hq_dvd_mul : q ∣ m * (a2 - 1) :=
        Nat.dvd_of_mul_dvd_mul_left hp_pos h


    -- 证明 gcd q m = 1
    have h_coprime : Nat.gcd q m = 1 :=
    coprime_div_gcd_div_gcd hp_pos

      --应用标准引理，除以最大公因数之后互质
    -- 应用欧几里得引理：因为gcd q m = 1 且 q ∣ m*(a2-1)，所以 q ∣ (a2-1)
    exact Coprime.dvd_of_dvd_mul_left h_coprime hq_dvd_mul

  -- 返回两个证明结果
  exact ⟨h_p_dvd_a1,  h_q_dvd_a2_sub_one⟩

----------------------------------------------------------------------------------

theorem ex15_results
  (a : ℕ → ℕ) (n k s : ℕ)
  (h_range : ∀ i, i ∈ A k → a i ∈ B n)
  (h_inj : ∀ n1 n2, n1 ∈ A k → n2 ∈ B n → a n1 = a n2 → n1 = n2)
  (h_dvd : ∀ i, i ∈ C k → n ∣ (a i) * (a (i + 1) - 1))
  (hk : 2 ≤ k) (hnk : k ≤ n) (hs : 1 ≤ s ∧ s ≤ k - 1) :
  ¬ n ∣ (a k) * ((a 1)-1) := by
------------------------
  have h_1_C : 1 ∈ C k := by
    simp [C]
    linarith
------------------ ----
  have h_n_dvd : n ∣ (a 1)*((a 2)-1) := by
    exact h_dvd 1 h_1_C
-----------------------
  have h_a1_le_n_pos : 1 ≤ a 1 ∧ a 1 ≤ n := by
    have h1_A : 1 ∈ A k := by simp [A]; linarith
    -- 应用 h_range 得到 a 1 ∈ B n
    have h_a1_B := h_range 1 h1_A
    -- 展开 B n 的定义
    simp [B] at h_a1_B
    exact ⟨h_a1_B.1, h_a1_B.2⟩
-----------------------
  have h_a2_le_n_pos :1 ≤ a 2 ∧ a 2 ≤ n := by
    have h2_A :2∈ A k := by simp [A]; linarith
    have h_a2_B := h_range 2 h2_A
    simp [B] at h_a2_B
    exact ⟨h_a2_B.1, h_a2_B.2⟩

  -- 应用lemma3得到p|a1和q|a2-1

---------------------------
  have h_lemma3 : n.gcd (a 1) ∣ a 1 ∧ n / n.gcd (a 1) ∣ a 2 - 1 := lemma3 h_a1_le_n_pos h_n_dvd
  set p := Nat.gcd n (a 1)
  set q := n / p
  have h_p_dvd_a1 : p ∣ a 1 := h_lemma3.1
  have h_q_dvd_a2_sub_1 : q ∣ (a 2) - 1 := h_lemma3.2
-------------------------
  have h_n_pq : n = p*q :=by
    rw [Nat.mul_div_cancel' (Nat.gcd_dvd_left n (a 1))]

--------------------------
  have q_dvd :∀ i,i∈ C k → q∣(a i) *(a (i +1) -1) :=by
    have q_dvd_1 : q∣p*q := Nat.dvd_mul_left q p
    have pq_dvd :∀ i,i∈ C k → p*q ∣(a i) *(a (i +1) -1) :=by
      rwa [h_n_pq] at h_dvd
    intro i hi  -- 引入具体的 i 和 hi
    exact dvd_trans q_dvd_1 (pq_dvd i hi)  -- 对具体的 i 应用

------------------------
-- 让 C 在 A 内部
  have h_C_in_A : C k ⊆ A k := by
    simp [A, C]
    intro x hx
    intro h_le_k_minus_1
    constructor
    exact hx
    exact Nat.le_trans h_le_k_minus_1 (Nat.sub_le k 1)

-- 为后面做准备
  have h_q_dvd_all : ∀ i ∈ C k, q ∣ ((a (i+1)) - 1) := by
    intro i hi
    have q_dvd_i : q ∣ a i * (a (i + 1) - 1) := q_dvd i hi
    have h_a_le_1 : 1 ≤ a i := by
      have h_mem : i ∈ A k := by
        exact h_C_in_A hi
      exact (h_range i h_mem).1

-- i 的范围分离,从C中形式分离
    have h_i_range : 1 ≤ i ∧ i ≤ k - 1 := hi
    have h_i_range_le : 1 ≤ i := h_i_range.1
    have h_i_range_ge : i ≤ k - 1 := h_i_range.2

-- 重要的归纳证明环节
    induction i, h_i_range_le using Nat.le_induction with
  -- 基本情况：i = 1 (对应证明 q ∣ a 2 - 1)
    | base =>
      ring_nf
      exact h_q_dvd_a2_sub_1
  -- 归纳步骤：i → i + 1,这里用j与j+1 ,避免变量重名
    | succ j hj h_ind =>
      have h_j_range_le : 1 ≤ j := by
        exact hj
      have h_j_range_ge : j ≤ k - 1 := by
        have h_j_le_j_plus_1 : j ≤ j + 1 := by
          exact Nat.le_add_right j 1
        exact Nat.le_trans h_j_le_j_plus_1 h_i_range_ge

      -- 证明 q ∣ a (j + 1) - 1,其实就是从基本情况中分离
      have h_dvd_jcc : q ∣ a (j + 1) - 1 := by
        have h_j_range : 1 ≤ j ∧ j ≤ k - 1 := by  --
          exact ⟨h_j_range_le, h_j_range_ge⟩
        have h_j_in_C : j ∈ C k := by --
          unfold C
          constructor
          exact h_j_range_le
          exact h_j_range_ge
        have h_dvd_j : q ∣ a j * (a (j + 1) - 1) := by  --
          exact q_dvd j h_j_in_C
        have h_a_le_2 : 1 ≤ a j := by --
          have h_mem : j ∈ A k := by
            exact h_C_in_A h_j_in_C
          exact (h_range j h_mem).1
        exact h_ind h_j_in_C h_dvd_j h_a_le_2 h_j_range h_j_range_ge
      exact lemma1 h_a_le_1 h_dvd_jcc q_dvd_i

---------------------------
  -- 特别地，取i = k-1
  have h_k_minus_1 : k-1 ∈ C k := by
    simp [C]
    linarith
  have h_k_eq : k - 1 + 1 = k := by
    rw [Nat.sub_add_cancel]
    exact Nat.le_of_succ_le hk  -- since hk : 2 ≤ k, we have 1 ≤ k

  have h_q_dvd_a_k_sub_1 : q ∣ (a k - 1) := by
    have h := h_q_dvd_all (k-1) h_k_minus_1
    rwa [h_k_eq] at h

------------------------------

  -- 现在我们有p | a 1和q | a k - 1
  have h_pq_dvd_a1_ak_sub_1 : (p * q) ∣ (a 1) * ((a k) - 1) := by
    exact Nat.mul_dvd_mul h_p_dvd_a1 h_q_dvd_a_k_sub_1
  have h_n_dvd_a1_ak_sub_1 :n∣(((a 1)*((a k)-1))):=by
    rwa [←h_n_pq] at h_pq_dvd_a1_ak_sub_1

---------------------

  -- 反证法：假设n | a k * (a 1 - 1)
  by_contra h_contr

  have h_ak_le_n_pos : 1 ≤ a k ∧ a k ≤ n:= by
    have hk_A : k∈ A k :=by simp[A];linarith
    have h_ak_B :=h_range k hk_A
    simp [B] at h_ak_B
    exact⟨h_ak_B.1, h_ak_B.2⟩
-------------------------------
  have h_different :(a k)≠ (a 1):=by
    by_contra h_eq
  -- 利用单射性 h_inj 推出 k = 1
    have h_k_eq_1 : k = 1 := h_inj k 1
      (by simp [A]; linarith)  -- 证明 k ∈ A k
      (by simp [B]; linarith)  -- 证明 1 ∈ B n
      h_eq
  -- 与 hk : 2 ≤ k 矛盾
    linarith [hk, h_k_eq_1]

----------------------
  --提升不等于关系到整数
  have h_different_int : (a k:ℤ )≠ (a 1 : ℤ ) :=by
    norm_cast
------------------------
  --提升整除关系到整数
  have h_n_dvd_a1_ak_sub_1_int :(n :ℤ )∣(((a 1)*((a k)-1)):ℤ ):=by
    have : (a 1 : ℤ) * ((a k : ℤ) - 1) = ↑(a 1 * (a k - 1)) := by
      rw [Nat.cast_mul, Nat.cast_sub (h_ak_le_n_pos.1), Nat.cast_one]
    rw [this]
    exact Int.natCast_dvd_natCast.mpr h_n_dvd_a1_ak_sub_1

  have h_contr_int :(n:ℤ )∣((a k)*((a 1)-1):ℤ ) :=by
    have :(a k :ℤ )*((a 1 :ℤ )-1) = ↑ (a k *(a 1 -1)):=by
      rw [Nat.cast_mul, Nat.cast_sub (h_a1_le_n_pos.1), Nat.cast_one]
    rw[this]
    exact Int.natCast_dvd_natCast.mpr h_contr

  have h_n_dvd_diff_int : (n : ℤ) ∣ (a k : ℤ) - (a 1 : ℤ) := by
  -- 首先将自然数整除关系转换为整数
    have h1 : (n : ℤ) ∣ (a 1 : ℤ) * ((a k : ℤ) - 1) := h_n_dvd_a1_ak_sub_1_int
    have h2 : (n : ℤ) ∣ (a k : ℤ) * ((a 1 : ℤ) - 1) := h_contr_int

  -- 展开表达式
    have h1_expanded : (n : ℤ) ∣ (a 1 : ℤ) * (a k : ℤ) - (a 1 : ℤ) := by
      rw [mul_sub, mul_one] at h1
      exact h1
    have h2_expanded : (n : ℤ) ∣ (a k : ℤ) * (a 1 : ℤ) - (a k : ℤ) := by
      rw [mul_sub, mul_one] at h2
      exact h2

  -- 计算差值
    have h_diff :
      (n : ℤ) ∣ ((a 1 : ℤ) * (a k : ℤ) - (a 1 : ℤ)) - ((a k : ℤ) * (a 1 : ℤ) - (a k : ℤ)) :=
      Int.dvd_sub h1_expanded h2_expanded

  -- 化简表达式
    simp only [mul_comm (a k : ℤ), sub_sub_sub_cancel_left] at h_diff
    exact h_diff
-------------------------

-- 提升不等式到整数
  have h_ak_int : 1 ≤ (a k : ℤ) ∧ (a k : ℤ) ≤ (n : ℤ) := by
    exact ⟨Nat.one_le_cast.mpr h_ak_le_n_pos.1, Nat.cast_le.mpr h_ak_le_n_pos.2⟩

  have h_a1_int : 1 ≤ (a 1 : ℤ) ∧ (a 1 : ℤ) ≤ (n : ℤ) := by
    exact ⟨Nat.one_le_cast.mpr h_a1_le_n_pos.1, Nat.cast_le.mpr h_a1_le_n_pos.2⟩
--应用引理2得矛盾
  exact lemma2 h_a1_int h_ak_int h_different_int h_n_dvd_diff_int

end NumberTheory
