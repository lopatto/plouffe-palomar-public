/-
Copyright (c) 2026 Patrick Lopatto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Lopatto
-/
module

public import Plouffe.Contracts
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Algebra.Ring.GeomSum

public section
namespace Plouffe.Proofs.Elementary

/-- The positive rational kernel for the first denominator family. -/
theorem oddKernel : Contracts.oddKernel := by
  intro q t hq ht
  have ht0 : 0 < t := by linarith
  have ht1 : t - 1 ≠ 0 := by linarith
  have ht2pos : 0 < t^2 - 1 := by nlinarith
  have ht2 : t^2 - 1 ≠ 0 := ne_of_gt ht2pos
  have ht4pos : 0 < t^4 - 1 := by nlinarith [sq_nonneg (t^2 - 1)]
  have ht4 : t^4 - 1 ≠ 0 := ne_of_gt ht4pos
  constructor
  · field_simp
    ring
  · apply div_pos
    · apply mul_pos ht0
      have hqt : 0 ≤ (q - 1)*t^2 := mul_nonneg (by linarith) (sq_nonneg t)
      nlinarith
    · exact ht4pos

/-- The ratio controlling the two consecutive series differences. -/
theorem deltaKernel : Contracts.deltaKernel := by
  intro t ht
  have ht0 : 0 < t := by linarith
  have ht1 : t - 1 ≠ 0 := by linarith
  have ht2pos : 0 < t^2 - 1 := by nlinarith
  have ht2 : t^2 - 1 ≠ 0 := ne_of_gt ht2pos
  have ht4pos : 0 < t^4 - 1 := by nlinarith [sq_nonneg (t^2 - 1)]
  have ht4 : t^4 - 1 ≠ 0 := ne_of_gt ht4pos
  have hd : 0 < 1/(t^2-1)-1/(t^4-1) := by
    apply sub_pos.mpr
    exact one_div_lt_one_div_of_lt ht2pos (by nlinarith [sq_nonneg (t^2-1)])
  constructor
  · apply (div_eq_iff (ne_of_gt hd)).2
    field_simp
    ring
  · apply (lt_of_mul_lt_mul_right ?_ ht0.le)
    have hsq : 0 < (t-1)^2 := sq_pos_of_pos (by linarith)
    have hti : t⁻¹*t = 1 := inv_mul_cancel₀ (ne_of_gt ht0)
    nlinarith

/-- Guarded powers and the rational definition of the odd denominator. -/
theorem oddCoefficients : Contracts.oddCoefficients := by
  intro m hm
  constructor
  · simpa using pow_le_pow_right₀ (by norm_num : (1:ℝ) ≤ 4) (by omega : 1 ≤ 2*m-1)
  constructor
  · have he : 4*m-2 = (2*m-1)*2 := by omega
    rw [he, pow_mul]
  · unfold D
    push_cast
    ring

/-- Euler reflection at the quarter arguments. -/
theorem gammaReflection : Contracts.gammaReflection := by
  change Real.Gamma (1/4)*Real.Gamma (3/4) = Real.pi*Real.sqrt 2
  have h := Real.Gamma_mul_Gamma_one_sub (1/4)
  have he : Real.pi*(1/4) = Real.pi/4 := by ring
  norm_num only [show (1:ℝ)-1/4 = 3/4 by norm_num] at h
  rw [he, Real.sin_pi_div_four] at h
  rw [h]
  have hs : Real.sqrt 2 ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr (by norm_num))
  have hsq := Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)
  field_simp
  nlinarith

/-- The finite inverse-power identity, obtained from the two-variable geometric sum. -/
theorem finitePartialFractions : Contracts.finitePartialFractions := by
  intro n X Y _hn hX hY hXY
  have hs : (∑ j ∈ Finset.range n, (-1:ℂ)^j*(X^(n-j))⁻¹*(Y^(j+1))⁻¹) =
      (∑ j ∈ Finset.range n, (-Y⁻¹)^j*(X⁻¹)^(n-1-j))*(X⁻¹*Y⁻¹) := by
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro j hj
    have hjn : j < n := Finset.mem_range.mp hj
    have hi : n-j = (n-1-j)+1 := by omega
    rw [hi, pow_add, pow_one, pow_add, pow_one]
    simp only [mul_inv_rev, inv_pow, show -Y⁻¹ = (-1:ℂ)*Y⁻¹ by ring, mul_pow]
    ring
  rw [hs]
  apply (div_eq_iff hXY).2
  have hg := (Commute.all (-Y⁻¹) X⁻¹).geom_sum₂_mul n
  have hi : X⁻¹*Y⁻¹*(X+Y) = -(-Y⁻¹-X⁻¹) := by
    field_simp
    ring
  calc
    (X^n)⁻¹-(-1:ℂ)^n*(Y^n)⁻¹ = -((-Y⁻¹)^n-(X⁻¹)^n) := by
      simp only [inv_pow, show -Y⁻¹ = (-1:ℂ)*Y⁻¹ by ring, mul_pow]
      ring
    _ = -((∑ j ∈ Finset.range n, (-Y⁻¹)^j*(X⁻¹)^(n-1-j))*(-Y⁻¹-X⁻¹)) := by rw [hg]
    _ = (∑ j ∈ Finset.range n, (-Y⁻¹)^j*(X⁻¹)^(n-1-j))*(X⁻¹*Y⁻¹)*(X+Y) := by
      rw [mul_assoc, hi]
      ring

/-- Nonzero denominator, simplification and bounds for the elimination coefficient. -/
theorem kCoefficients : Contracts.kCoefficients := by
  intro m hm
  let q : ℚ := (-4:ℚ)^m
  have hqabs : 4 ≤ |q| := by
    dsimp [q]
    rw [abs_pow]
    norm_num only [abs_neg, abs_of_nonneg (by norm_num : (0:ℚ) ≤ 4)]
    simpa using pow_le_pow_right₀ (by norm_num : (1:ℚ) ≤ 4) hm
  have hq1 : 1-q ≠ 0 := by
    intro h
    have : q = 1 := by linarith
    rw [this] at hqabs
    norm_num at hqabs
  have hq2 : 2*q+1 ≠ 0 := by
    intro h
    have : q = -(1/2:ℚ) := by linarith
    rw [this] at hqabs
    norm_num at hqabs
  have hp4 : (4:ℚ)^(2*m) = (16:ℚ)^m := by
    rw [pow_mul]
    norm_num
  have hp2 : (2:ℚ)^(4*m+1) = 2*(16:ℚ)^m := by
    rw [pow_add, pow_one, pow_mul]
    norm_num
    ring
  have hqq : q^2 = (16:ℚ)^m := by
    dsimp [q]
    rw [← pow_mul, mul_comm m 2, pow_mul]
    norm_num
  have hdq : 1+q-2*q^2 ≠ 0 := by
    rw [show 1+q-2*q^2 = (1-q)*(2*q+1) by ring]
    exact mul_ne_zero hq1 hq2
  have hd : 1+(-4:ℚ)^m-(2:ℚ)^(4*m+1) ≠ 0 := by
    rw [hp2, ← hqq]
    exact hdq
  have hk : K m = (q+1)/(2*(2*q+1)) := by
    unfold K
    rw [hp4, hp2, ← hqq]
    change ((1-q^2)/2)/(1+q-2*q^2) = (q+1)/(2*(2*q+1))
    rw [div_div]
    apply (div_eq_div_iff (mul_ne_zero (by norm_num) hdq) (mul_ne_zero (by norm_num) hq2)).2
    ring
  have hkr : (K m:ℝ) = (((-4:ℝ)^m+1)/(2*(2*(-4:ℝ)^m+1))) := by
    have hk' := hk
    dsimp [q] at hk'
    exact_mod_cast hk'
  have hq2r : 2*(-4:ℝ)^m+1 ≠ 0 := by
    have hq2' := hq2
    dsimp [q] at hq2'
    exact_mod_cast hq2'
  refine ⟨hd,hk,?_,?_,?_,?_,?_,?_⟩
  · exact_mod_cast hp4
  · exact_mod_cast hp2
  · simpa using pow_le_pow_right₀ (by norm_num : (1:ℝ) ≤ 16) hm
  · rw [abs_pow]
    norm_num only [abs_neg, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 4)]
    simpa using pow_le_pow_right₀ (by norm_num : (1:ℝ) ≤ 4) hm
  · have hqqr : ((-4:ℝ)^m)^2 = (16:ℝ)^m := by
      have hqq' := hqq
      dsimp [q] at hqq'
      exact_mod_cast hqq'
    have hkmul := (eq_div_iff (mul_ne_zero (by norm_num : (2:ℝ) ≠ 0) hq2r)).1 hkr
    have ha : (2*(K m:ℝ)*(2*((-4:ℝ)^m)^2-(-4:ℝ)^m+1)-((-4:ℝ)^m)^2)*(2*(-4:ℝ)^m+1) = 1 := by
      linear_combination (2*((-4:ℝ)^m)^2-(-4:ℝ)^m+1)*hkmul
    have hb := (eq_div_iff hq2r).2 ha
    rw [hqqr] at hb
    linarith
  · have hkmul := (eq_div_iff (mul_ne_zero (by norm_num : (2:ℝ) ≠ 0) hq2r)).1 hkr
    apply (eq_div_iff hq2r).2
    nlinarith [hkmul]

#print axioms kCoefficients
#print axioms finitePartialFractions
#print axioms oddKernel
#print axioms deltaKernel
#print axioms oddCoefficients
#print axioms gammaReflection

end Plouffe.Proofs.Elementary
