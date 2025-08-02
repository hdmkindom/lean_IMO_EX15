import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.Analysis.Normed.Group.Basic

open Real

namespace TrigProof

variable {x y z : ℝ}
variable (hx : |x| ≠ 1 / sqrt 3) (hy : |y| ≠ 1 / sqrt 3) (hz : |z| ≠ 1 / sqrt 3)
variable (hxyz : x + y + z = x * y * z)



lemma tan_three_mul (t : ℝ) (ht : cos (3 * arctan t) ≠ 0) :
  tan (3 * arctan t) * (1 - 3 * t ^ 2) = (3 * t - t ^ 3)  :=by
  rw [tan_eq_sin_div_cos]
  set θ := arctan t with hθ
  field_simp [ht]
  rw [sin_three_mul, cos_three_mul]
  have h_tan_theta : t = tan θ := by
    rw [hθ] 
    rw [tan_arctan]
  rw [h_tan_theta, tan_eq_sin_div_cos]
  have hcosθ : cos θ ≠ 0 := by
    rw [cos_arctan]
    apply ne_of_gt
    exact one_div_pos.2 (sqrt_pos.2 (add_pos_of_pos_of_nonneg zero_lt_one (sq_nonneg t)))
  field_simp[hcosθ]
  ring_nf

  have h11 : cos θ ^ 8 =  cos θ ^ 6 *(1 - sin θ ^ 2) := by
    have h12 : cos θ ^ 8 = cos θ ^ 6 * cos θ ^ 2 := by
      ring
    rw [h12]
    have h13 : cos θ ^ 2 = 1 - sin θ ^ 2 := by
      have h14 : sin θ ^ 2 + cos θ ^ 2 = 1 := Real.sin_sq_add_cos_sq θ
      rw [add_comm] at h14
      exact eq_sub_of_add_eq h14
    rw [h13]
  rw [h11]
  ring_nf

  have h21 : sin θ ^3 * cos θ ^ 6 = sin θ ^3* cos θ ^ 4 *(1 - sin θ ^ 2) := by
    have h22 : sin θ ^3 * cos θ ^ 6 = sin θ ^3 * cos θ ^ 4 * cos θ ^ 2 := by
      ring
    rw [h22]
    have h13 : cos θ ^ 2 = 1 - sin θ ^ 2 := by
      have h14 : sin θ ^ 2 + cos θ ^ 2 = 1 := Real.sin_sq_add_cos_sq θ
      rw [add_comm] at h14
      exact eq_sub_of_add_eq h14
    rw [h13]
  rw [h21]
  ring
-----------------------------------------------------

lemma kpi_zero (α β γ : ℝ) (k: ℤ) (h1 : cos α ≠ 0) (h2 : cos β ≠ 0) (h3 : cos γ ≠ 0) (h6 : cos α * cos β * cos γ ≠ 0) (h: tan α + tan β + tan γ = tan α * tan β * tan γ) : sin (α + β + γ) = sin (k * π) := by

  
  rw [Real.sin_int_mul_pi]
  rw [sin_add]
  rw [sin_add,cos_add]
  ring_nf
  have h32 : sin α * cos β * cos γ + cos α * sin β * cos γ + cos α * cos β * sin γ - sin α * sin β * sin γ = 0 := by
    have h41 : sin α = tan α * cos α := by
      rw[tan_eq_sin_div_cos]
      field_simp
    have h42 : sin β = tan β * cos β := by
      rw[tan_eq_sin_div_cos]
      field_simp
    have h43 : sin γ = tan γ * cos γ := by
      rw[tan_eq_sin_div_cos]
      field_simp  
    rw[h41,h42,h43]
    ring_nf
    have h51 : tan α * cos α * cos β * cos γ = cos α * cos β * cos γ * tan α := by
      ring
    rw [h51]
    set a := cos α * cos β * cos γ with h0
    have h61 : a ≠ 0 := by
      rw [h0]
      exact h6    
    have h52 : a * (tan α - tan α * tan β * tan γ + tan β + tan γ) =  a * tan α - a * tan α * tan β * tan γ + a * tan β + a * tan γ  :=by
      ring
    have h_eq : a * (tan α - tan α * tan β * tan γ + tan β + tan γ) = 0 := by
      rw [← h] -- 使用题设条件 tan α + tan β + tan γ = tan α * tan β * tan γ
      ring
    have h_eq' : a * (tan α - tan α * tan β * tan γ + tan β + tan γ) = a * 0 := by
      simpa [mul_zero] using h_eq 
    have h_final :tan α - tan α * tan β * tan γ + tan β + tan γ = 0 :=
     (mul_right_inj' h61).mp h_eq'
    rw [← h52, h_final]
    ring

  rw [← h32]
  ring


--------------------------------------------------------------------------
lemma cos_three_arctan_ne_zero (t : ℝ) (ht : |t| ≠ 1 / sqrt 3) : cos (3 * arctan t) ≠ 0 := by
  -- 设 θ = arctan t
  set θ := arctan t with hθ
  -- 展开三倍角公式
  rw [cos_three_mul]
  ring_nf
  have hfactor : -(cos θ * 3) + cos θ ^ 3 * 4 = cos θ * (4 * cos θ ^ 2 - 3) := by
    ring         -- ring 可以帮我们做这种因式分解
  -- 用重写把目标换成乘积形式
  rw [hfactor]
  have hcosθ : cos θ ≠ 0 := by
    -- θ = arctan t
    rw [hθ, cos_arctan]
    -- cos (arctan t) = 1 / sqrt (1 + t^2) ，显然非零
    apply ne_of_gt
    rw [one_div_pos]
    apply sqrt_pos.2
    linarith [sq_nonneg t]
  have hcos2 : 4 * cos θ ^ 2 - 3 ≠ 0 := by
    rw [hθ, cos_arctan]  -- 把 cos θ 展开成 arctan t 的表达式
    field_simp           -- 清除分母，化简目标为 1 - 3 * t^2 ≠ 0
    intro h              -- 假设等于 0，推出矛盾
    -- 把 1 - 3 * t^2 = 0 变为 t^2 = 1/3 ⇒ |t| = 1/√3
    have ht2 : t ^ 2 = 1 / 3 := by linarith
    have habs : |t| = sqrt (t ^ 2) := by
      rw [Real.sqrt_sq_eq_abs]
    rw [ht2] at habs
    have hsqrt3:√(1 / 3)=1 / √3 := by
      rw [Real.sqrt_div]
      rw[Real.sqrt_one]
      norm_num
    rw[hsqrt3] at habs
    exact ht habs
  exact mul_ne_zero hcosθ hcos2

----------------------------------------------------------------------------------------------------

theorem problem (x y z : ℝ) (k: ℤ)
  (hx : abs x ≠ 1 / sqrt 3)
  (hy : abs y ≠ 1 / sqrt 3)
  (hz : abs z ≠ 1 / sqrt 3)
  (hcond : x + y + z = x * y * z) :
  (3*x - x^3) / (1 - 3*x^2) + (3*y - y^3) / (1 - 3*y^2) + (3*z - z^3) / (1 - 3*z^2) =
  ((3*x - x^3) / (1 - 3*x^2)) * ((3*y - y^3) / (1 - 3*y^2)) * ((3*z - z^3) / (1 - 3*z^2)) := by
  set α := arctan x with hα
  set β := arctan y with hβ
  set γ := arctan z with hγ
  have hxtan : x= tan α :=by
     rw [hα]
     rw [tan_arctan]
  have hytan : y= tan β :=by
     rw [hβ]
     rw [tan_arctan]
  have hztan : z= tan γ :=by
     rw [hγ]
     rw [tan_arctan]
  rw[hxtan,hytan,hztan]
  have hthree1:(3 * tan α - tan α ^ 3) / (1 - 3 * tan α ^ 2) = tan (3*α) := by
    have hcos : cos (3 * arctan x) ≠ 0 := cos_three_arctan_ne_zero x hx
    have htan3 : tan (3 * arctan x)  * (1 - 3 * x^2) = (3 * x - x^3) := tan_three_mul x hcos
    rw [← hα] at htan3
    rw [hxtan] at htan3
    have denom_ne_zero : 1 - 3 * tan α ^ 2 ≠ 0 := by
      rw [← hxtan] 
      intro h
      have hx2 : x ^ 2 = 1 / 3 := by linarith
      have habs2 : |x| = sqrt (x ^ 2) := by
        rw [Real.sqrt_sq_eq_abs]
      have hx2sqrt: Real.sqrt (x ^ 2) = Real.sqrt (1 / 3) := by rw [hx2]
      have hh: |x| = 1 / Real.sqrt 3 := by
        rw [habs2, hx2sqrt]
        rw [Real.sqrt_div]
        rw[Real.sqrt_one]
        norm_num
      exact hx hh
    exact Eq.symm ((eq_div_iff_mul_eq denom_ne_zero).mpr htan3)
  have hthree2:(3 * tan β - tan β ^ 3) / (1 - 3 * tan β ^ 2) = tan (3*β) := by
    have hcos : cos (3 * arctan y) ≠ 0 := cos_three_arctan_ne_zero y hy
    have htan3 : tan (3 * arctan y)  * (1 - 3 * y^2) = (3 * y - y^3) := tan_three_mul y hcos
    rw [← hβ] at htan3
    rw [hytan] at htan3
    have denom_ne_zero : 1 - 3 * tan β ^ 2 ≠ 0 := by
      rw [← hytan] 
      intro h
      have hy2 : y ^ 2 = 1 / 3 := by linarith
      have habs2 : |y| = sqrt (y ^ 2) := by
        rw [Real.sqrt_sq_eq_abs]
      have hy2sqrt: Real.sqrt (y ^ 2) = Real.sqrt (1 / 3) := by rw [hy2]
      have hh: |y| = 1 / Real.sqrt 3 := by
        rw [habs2, hy2sqrt]
        rw [Real.sqrt_div]
        rw[Real.sqrt_one]
        norm_num
      exact hy hh
    exact Eq.symm ((eq_div_iff_mul_eq denom_ne_zero).mpr htan3)
  have hthree3:(3 * tan γ - tan γ ^ 3) / (1 - 3 * tan γ ^ 2) = tan (3*γ) := by
    have hcos : cos (3 * arctan z) ≠ 0 := cos_three_arctan_ne_zero z hz
    have htan3 : tan (3 * arctan z)  * (1 - 3 * z^2) = (3 * z - z^3) := tan_three_mul z hcos
    rw [← hγ] at htan3
    rw [hztan] at htan3
    have denom_ne_zero : 1 - 3 * tan γ ^ 2 ≠ 0 := by
      rw [← hztan] 
      intro h
      have hz2 : z ^ 2 = 1 / 3 := by linarith
      have habs2 : |z| = sqrt (z ^ 2) := by
        rw [Real.sqrt_sq_eq_abs]
      have hz2sqrt: Real.sqrt (z ^ 2) = Real.sqrt (1 / 3) := by rw [hz2]
      have hh: |z| = 1 / Real.sqrt 3 := by
        rw [habs2, hz2sqrt]
        rw [Real.sqrt_div]
        rw[Real.sqrt_one]
        norm_num
      exact hz hh
    exact Eq.symm ((eq_div_iff_mul_eq denom_ne_zero).mpr htan3)
  rw[hthree1,hthree2,hthree3]
  have final:tan (3 * α) + tan (3 * β) + tan (3 * γ) - tan (3 * α) * tan (3 * β) * tan (3 * γ) =0 :=by
    rw [tan_eq_sin_div_cos, tan_eq_sin_div_cos, tan_eq_sin_div_cos]
    have hcosα := cos_three_arctan_ne_zero x hx
    rw [← hα] at hcosα
    have hcosβ := cos_three_arctan_ne_zero y hy
    rw [← hβ] at hcosβ
    have hcosγ := cos_three_arctan_ne_zero z hz
    rw [← hγ] at hcosγ
    field_simp [hcosα, hcosβ, hcosγ]
    ring_nf
    have hsumall : sin (3 * α) * cos (3 * β) * cos (3 * γ) +
          cos (3 * α) * sin (3 * β) * cos (3 * γ) +
          cos (3 * α) * cos (3 * β) * sin (3 * γ) -
          sin (3 * α) * sin (3 * β) * sin (3 * γ) = sin (3 * (α + β + γ)) := by
      -- 令 X = 3α, Y = 3β, Z = 3γ
      set X := 3 * α with hX
      set Y := 3 * β with hY
      set Z := 3 * γ with hZ

      -- 利用 sin(x + y) = sin x cos y + cos x sin y
      have step1 : sin (X + Y) = sin X * cos Y + cos X * sin Y := sin_add X Y


      -- 利用 cos(x + y) = cos x cos y - sin x sin y
      have step2 : cos (X + Y)=cos X * cos Y - sin X * sin Y  := cos_add X Y

      have hsum : sin X * cos Y * cos Z + cos X * sin Y * cos Z + cos X * cos Y * sin Z - sin X * sin Y * sin Z= (sin X * cos Y + cos X * sin Y) * cos Z + (cos X * cos Y - sin X * sin Y) * sin Z := by ring
      rw[hsum]
      rw [step1.symm, step2.symm]
      have hsum2 : sin (X + Y) * cos Z + cos (X + Y) * sin Z = sin (X + Y + Z) := (sin_add (X + Y) Z).symm
      rw[hsum2]
      rw [hX, hY, hZ]
      have h_sum : sin (3 * α + 3 * β + 3 * γ) = sin (3 * (α + β + γ)) := by
        rw [← mul_add, ← mul_add]
      rw[h_sum]
    have hhh : sin (3 * α) * cos (3 * β) * cos (3 * γ) + cos (3 * α) * sin (3 * β) * cos (3 * γ) +cos (3 * α) * cos (3 * β) * sin (3 * γ) -sin (3 * α) * sin (3 * β) * sin (3 * γ) =sin (α * 3) * cos (β * 3) * cos (γ * 3) - sin (α * 3) * sin (β * 3) * sin (γ * 3) +cos (β * 3) * cos (α * 3) * sin (γ * 3) +sin (β * 3) * cos (α * 3) * cos (γ * 3) :=by
      ring_nf
    rw[← hhh]
    rw[hsumall]
    have hk : sin (k * π) = 0 := by
      simp [Real.sin_int_mul_pi]
    have hcosα : cos α ≠ 0 := by
      -- θ = arctan t
      rw [hα, cos_arctan]
      -- cos (arctan t) = 1 / sqrt (1 + t^2) ，显然非零
      apply ne_of_gt
      rw [one_div_pos]
      apply sqrt_pos.2
      linarith [sq_nonneg x]
    have hcosβ : cos β ≠ 0 := by
      -- θ = arctan t
      rw [hβ, cos_arctan]
      -- cos (arctan t) = 1 / sqrt (1 + t^2) ，显然非零
      apply ne_of_gt
      rw [one_div_pos]
      apply sqrt_pos.2
      linarith [sq_nonneg y]
    have hcosγ : cos γ ≠ 0 := by
      -- θ = arctan t
      rw [hγ, cos_arctan]
      -- cos (arctan t) = 1 / sqrt (1 + t^2) ，显然非零
      apply ne_of_gt
      rw [one_div_pos]
      apply sqrt_pos.2
      linarith [sq_nonneg z]
    have hprod : cos α * cos β * cos γ ≠ 0 := by
      apply mul_ne_zero
      apply mul_ne_zero
      exact hcosα
      exact hcosβ
      exact hcosγ
    have h1:tan α + tan β + tan γ = tan α * tan β * tan γ :=by
      rw [← hxtan, ← hytan, ← hztan]
      exact hcond
    have hsum : sin (α + β + γ) = sin (k * π) :=kpi_zero α β γ k hcosα hcosβ hcosγ hprod h1
    have hzero : sin (↑k * π) = 0 := Real.sin_int_mul_pi k
    rw [hzero] at hsum
    have final2 : sin (3 * (α + β + γ)) = 0 := by
      set θ := α + β + γ with hθ
      have hsin := hsum
      rw [hθ] at hsin
      rw [sin_three_mul θ]
      rw [hsin]
      simp
    exact final2
  have h_eq := eq_of_sub_eq_zero final
  exact h_eq

    

      



