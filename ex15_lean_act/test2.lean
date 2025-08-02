import Mathlib

open Real

theorem test2 (x y z : ℝ)
    (hx : |x| ≠ 1 / √3) (hy : |y| ≠ 1 / √3) (hz : |z| ≠ 1 / √3)
    (h : x + y + z = x * y * z) :
    (3 * x - x ^ 3) / (1 - 3 * x ^ 2) + (3 * y - y ^ 3) / (1 - 3 * y ^ 2) +
    (3 * z - z ^ 3) / (1 - 3 * z ^ 2) =
    (3 * x - x ^ 3) / (1 - 3 * x ^ 2) * (3 * y - y ^ 3) / (1 - 3 * y ^ 2) *
    (3 * z - z ^ 3) / (1 - 3 * z ^ 2) := by
  have : |1 / √3| = 1 / √3 := by simp
  have eq {x : ℝ} (hx : |x| ≠ 1 / √3) : (1 - 3 * x ^ 2) ≠ 0 := by
    rw [mul_comm]
    rw [show 1 - x ^ 2 * 3 ≠ 0 ↔ 1 / 3 ≠ x ^ 2 by field_simp [sub_eq_zero]]
    rw [show 1 / 3 = (1 / √3) ^ 2 by norm_num]
    rw [(sq_eq_sq_iff_abs_eq_abs _ _).ne]
    rw [this]
    exact hx.symm
  field_simp [eq hx, eq hy, eq hz]
  nlinarith [sq_nonneg (x * y + y * z + z * x - 1), sq_nonneg (x * y * z - (x + y + z)), sq_nonneg (x ^ 2 + y ^ 2 + z ^ 2 - 1)]
