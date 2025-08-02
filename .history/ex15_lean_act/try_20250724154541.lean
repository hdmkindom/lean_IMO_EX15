import Mathlib.Data.Fin.Basic
import Mathlib.NumberTheory.Coprime.Basic
import Mathlib.NumberTheory.Zsqrtd.GaussianInt
import Mathlib.Data.Nat.ModEq
import Mathlib.Algebra.BigOperators.Fin

open Nat

-- 定义在 NumberTheory 命名空间中
namespace NumberTheory

-- Lean 4 定理证明
-- 变量声明与题目保持一致
variable {n k : ℕ} (hn : 0 < n) (hk : 2 ≤ k)
variable {a : Fin k → ℕ} (ha_inj : Function.Injective a)
variable (ha_range : ∀ i, a i ∈ Set.Icc (1 : ℕ) n)

/--
  设 `n` 为正整数, `k ≥ 2`。
  `a : Fin k → ℕ` 是一个序列, 其值在 `1` 到 `n` 之间且互不相同。
  如果对于所有 `i` 从 `0` 到 `k-2`, 都有 `n ∣ aᵢ * (aᵢ₊₁ - 1)`，
  那么 `n` 不整除 `aₖ₋₁ * (a₀ - 1)`。
-/
theorem IMO_2006_N5
    -- 题设条件: n 整除链 a₀(a₁-1), a₁(a₂-1), ..., aₖ₋₂(aₖ₋₁-1)
    (hdiv : ∀ i : Fin (k - 1), n ∣ a (Fin.castSucc i) * (a i.succ - 1)) :
    -- 结论: n 不整除链的最后一个环节 aₖ₋₁(a₀-1)
    ¬ (n ∣ a (Fin.last (k-1)) * (a 0 - 1)) := by
  -- 1. 使用反证法, 假设结论不成立
  by_contra h_contra

  -- 为了方便, 定义循环后继函数 aᵢ₊₁
  let succ (i : Fin k) : Fin k := i + 1

  -- 2. 将题设和反证假设合并成一个完整的循环整除关系
  --    证明: ∀ i ∈ Fin k, n ∣ aᵢ * (aᵢ₊₁ - 1)
  have h_cycle : ∀ i : Fin k, n ∣ a i * (a (succ i) - 1) := by
    -- 使用 Fin.lastCases, 分两种情况讨论 i:
    -- a) i 是最后一个元素 k-1
    -- b) i 不是最后一个元素 (i < k-1)
    refine Fin.lastCases ?h_last ?h_nonlast
    · -- a) 当 i = k-1 时, i+1 = 0 (循环回来), 证明 n ∣ aₖ₋₁ * (a₀ - 1)
      -- 这正是我们的反证假设 h_contra
      rw [Fin.add_one_last]
      exact h_contra
    · -- b) 当 i < k-1 时, 我们可以将 i : Fin k 视作 i' : Fin (k-1)
      intro i'
      -- 证明 n ∣ aᵢ' * (aᵢ'₊₁ - 1)
      -- 这正是题设条件 hdiv i'
      -- `Fin.castSucc i'` 在 Fin k 中代表 i'
      -- `i'.succ` 在 Fin k 中代表 i'+1
      -- Mathlib 中 `Fin.castSucc i' + 1` 等于 `i'.succ` 提升到 Fin k
      simp_rw [succ, Fin.coe_castSucc, Fin.coe_succ]
      exact hdiv i'

  -- 3. 定义 gᵢ = gcd(aᵢ, n), 并推导关键性质
  let g (i : Fin k) : ℕ := gcd (a i) n
  have hg_dvd_a (i : Fin k) : g i ∣ a i := gcd_dvd_left (a i) n

  -- 证明: 对于循环中的每一步, n / gᵢ ∣ aᵢ₊₁ - 1
  have h_div_succ_minus_one : ∀ i, n / g i ∣ a (succ i) - 1 := by
    intro i
    -- 由 h_cycle: n ∣ aᵢ * (aᵢ₊₁ - 1)
    -- 且 gcd(aᵢ/gᵢ, n/gᵢ) = 1 (这是 gcd_coprime_div_left_right)
    -- 根据欧几里得引理, 可得 n/gᵢ ∣ aᵢ₊₁ - 1
    exact Coprime.dvd_of_dvd_mul_left (gcd_coprime_div_left_right (hg_dvd_a i)) (h_cycle i)

  -- 证明: gᵢ₊₁ 和 n / gᵢ 互质
  have hg_coprime : ∀ i, Coprime (g (succ i)) (n / g i) := by
    intro i
    -- 设 d 是 gᵢ₊₁ 和 n/gᵢ 的公因子
    apply Coprime.of_dvd
    intro d hd_g_succ hd_n_div_g
    -- d | gᵢ₊₁ => d | aᵢ₊₁
    have hd_a_succ : d ∣ a (succ i) := dvd_trans hd_g_succ (hg_dvd_a (succ i))
    -- d | n/gᵢ 且 aᵢ₊₁ ≡ 1 (mod n/gᵢ) => d | aᵢ₊₁ - 1
    have hd_a_succ_minus_1 : d ∣ a (succ i) - 1 :=
      dvd_trans hd_n_div_g (dvd_of_mod_eq_one (h_div_succ_minus_one i))
    -- d 同时整除 aᵢ₊₁ 和 aᵢ₊₁ - 1, 则 d 整除它们的差 1, 故 d = 1
    exact dvd_one.mp (dvd_sub (dvd_refl _) hd_a_succ hd_a_succ_minus_1)

  -- 证明: gᵢ₊₁ 整除 gᵢ
  have hg_dvd_chain : ∀ i, g (succ i) ∣ g i := by
    intro i
    -- 已知 gᵢ₊₁ | n 且 gcd(gᵢ₊₁, n/gᵢ) = 1
    -- 这意味着 gᵢ₊₁ 的所有素因子在 n 中的幂次都和在 gᵢ 中的幂次相同
    -- 从而 gᵢ₊₁ | gᵢ
    apply Coprime.dvd_of_dvd_of_dvd_mul (hg_coprime i).symm (gcd_dvd_right _ _)
    rw [mul_comm]
    apply dvd_mul_of_dvd_left (hg_dvd_a i)

  -- 4. 证明所有 gᵢ 都相等
  have hg_const : ∀ i j : Fin k, g i = g j := by
    -- 我们已经有了一个整除环: g₀ | gₖ₋₁ | ... | g₁ | g₀
    -- 在正整数中, 这意味着它们必须全部相等
    suffices ∀ i, g 0 = g i by intro i j; rw [this i, this j]
    intro i
    -- 证明 gᵢ | g₀ 和 g₀ | gᵢ
    apply dvd_antisymm
    · -- 证明 gᵢ | g₀
      -- gᵢ | gᵢ₋₁ | ... | g₀
      induction i using Fin.induction with
      | zero => rfl
      | step i ih => exact dvd_trans (hg_dvd_chain i) ih
    · -- 证明 g₀ | gᵢ
      -- g₀ | gₖ₋₁ | ... | gᵢ
      let i_rev := Fin.rev i
      suffices h_rev : ∀ j, g 0 ∣ g (Fin.rev j) by exact h_rev i_rev
      intro j
      induction j using Fin.induction with
      | zero => rw [Fin.rev_zero]; exact hg_dvd_chain (Fin.last (k-1))
      | step j ih => rw [Fin.rev_succ]; exact dvd_trans ih (hg_dvd_chain (Fin.rev j - 1))

  -- 5. 设公共的 gcd 为 g₀, 并证明 g₀ 与 n/g₀ 互质
  let g₀ := g 0
  have hg_eq (i : Fin k) : g i = g₀ := (hg_const i 0).symm
  have h_coprime_g₀ : Coprime g₀ (n / g₀) := by
    rw [← hg_eq 0, ← hg_eq 1]
    exact hg_coprime 0

  -- 6. 应用中国剩余定理
  -- 证明所有 aᵢ 都满足同一个同余方程组: x ≡ 0 (mod g₀), x ≡ 1 (mod n/g₀)
  have ha_solves_crt : ∀ i, a i ≡ 0 [MOD g₀] ∧ a i ≡ 1 [MOD n / g₀] := by
    intro i
    constructor
    · -- aᵢ ≡ 0 [MOD g₀]
      rw [ModEq.comm, ← dvd_iff_mod_eq_zero]
      rw [← hg_eq i]; exact hg_dvd_a i
    · -- aᵢ ≡ 1 [MOD n / g₀]
      rw [ModEq, ← hg_eq (i-1)]
      exact mod_eq_one_of_dvd (h_div_succ_minus_one (i-1))

  -- 根据中国剩余定理的解的唯一性, 所有 aᵢ 必须相等
  have ha_eq_all : ∀ i j, a i = a j := by
    intro i j
    apply ModEq.eq_of_lt_of_lt
    · apply ModEq.crt_solution_unique' hn h_coprime_g₀ (ha_solves_crt i) (ha_solves_crt j)
    · exact (ha_range i).2
    · exact (ha_range j).2

  -- 7. 导出最终矛盾
  -- 因为 k ≥ 2, 我们可以取两个不同的索引 0 和 1
  have h_ne : (0 : Fin k) ≠ 1 := by
    apply Fin.ne_of_val_ne; norm_num; linarith [hk]
  -- `a 0 = a 1` 与 `a` 是单射 (ha_inj) 的前提矛盾
  exact ha_inj.ne h_ne (ha_eq_all 0 1)

end NumberTheory
