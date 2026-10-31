/-
Copyright (c) 2026 Patrick Lopatto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Lopatto
-/
module

public import Plouffe.Proofs.Gamma.Beta
public import Plouffe.Proofs.Elementary
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

public section
open MeasureTheory Set intervalIntegral
namespace Plouffe.Proofs.Gamma

private noncomputable def betaKernel (x : ℝ) : ℝ := x^(-(3:ℝ)/4)*(1-x)^(-(1:ℝ)/2)
private noncomputable def complexBetaKernel (x : ℝ) : ℂ :=
  (x:ℂ)^((1/4:ℂ)-1)*(1-(x:ℂ))^((1/2:ℂ)-1)

private theorem complexBeta_eq_real (x : ℝ) (hx0 : 0 < x) (hx1 : x < 1) :
    complexBetaKernel x = (betaKernel x:ℂ) := by
  norm_num [complexBetaKernel,betaKernel,Complex.ofReal_mul,Complex.ofReal_cpow hx0.le,
    Complex.ofReal_cpow (sub_nonneg.mpr hx1.le)]

private theorem betaKernel_integrable : IntervalIntegrable betaKernel volume 0 1 := by
  have hC : IntervalIntegrable complexBetaKernel volume 0 1 :=
    Complex.betaIntegral_convergent (by norm_num) (by norm_num)
  have hR : IntervalIntegrable (fun x => (complexBetaKernel x).re) volume 0 1 := ⟨hC.1.re,hC.2.re⟩
  apply hR.congr_uIoo
  intro x hx
  have hx' : x ∈ Ioo (0:ℝ) 1 := by simpa only [uIoo_of_le (by norm_num : (0:ℝ)≤1)] using hx
  change (complexBetaKernel x).re = betaKernel x
  rw [complexBeta_eq_real x hx'.1 hx'.2]
  rfl

private theorem integral_betaKernel :
    (∫ x : ℝ in (0:ℝ)..1, betaKernel x) = Real.Gamma (1/4)*Real.sqrt Real.pi/Real.Gamma (3/4) := by
  have hC : IntervalIntegrable complexBetaKernel volume 0 1 :=
    Complex.betaIntegral_convergent (by norm_num) (by norm_num)
  calc
    _ = ∫ x : ℝ in (0:ℝ)..1, (complexBetaKernel x).re := by
      apply integral_congr_uIoo
      intro x hx
      have hx' : x ∈ Ioo (0:ℝ) 1 := by simpa only [uIoo_of_le (by norm_num : (0:ℝ)≤1)] using hx
      change betaKernel x = (complexBetaKernel x).re
      rw [complexBeta_eq_real x hx'.1 hx'.2]
      rfl
    _ = (Complex.betaIntegral (1/4) (1/2)).re := by
      exact intervalIntegral_re hC
    _ = _ := by rw [beta_quarter_half]; rfl

private theorem substitution_kernel (x : ℝ) (hx0 : 0 < x) (hx1 : x < 1) :
    betaKernel (x^4)*(4*x^3) = 4*(1/Real.sqrt (1-x^4)) := by
  have hx4 : x^4 < 1 := pow_lt_one₀ hx0.le hx1 (by norm_num)
  have hpow : (x^4)^(-(3:ℝ)/4) = (x^3)⁻¹ := by
    rw [← Real.rpow_natCast_mul hx0.le]
    norm_num [Real.rpow_neg hx0.le]
  have hroot : (1-x^4)^(-(1:ℝ)/2) = 1/Real.sqrt (1-x^4) := by
    rw [show -(1:ℝ)/2 = -(1/2:ℝ) by ring,Real.rpow_neg (sub_nonneg.mpr hx4.le),← Real.sqrt_eq_rpow,one_div]
  unfold betaKernel
  rw [hpow,hroot]
  calc
    _ = 4*((x^3)⁻¹*x^3)*(1/Real.sqrt (1-x^4)) := by ring
    _ = _ := by rw [inv_mul_cancel₀ (pow_ne_zero _ (ne_of_gt hx0)),mul_one]

/-- The lemniscatic integral is integrable, and its value follows from a legitimate quartic substitution. -/
theorem lemniscatic_integral :
    IntervalIntegrable (fun x : ℝ => 1/Real.sqrt (1-x^4)) volume 0 1 ∧
      (∫ x : ℝ in (0:ℝ)..1, 1/Real.sqrt (1-x^4)) =
        Real.Gamma (1/4)^2/(4*Real.sqrt (2*Real.pi)) := by
  have hf : ContinuousOn (fun x : ℝ => x^4) (uIcc 0 1) := (continuous_id.pow 4).continuousOn
  have hd : ∀ x ∈ Ioo (min (0:ℝ) 1) (max 0 1), HasDerivAt (fun x : ℝ => x^4) (4*x^3) x := by
    intro x hx
    simpa only [Nat.cast_ofNat,Nat.reduceSub] using hasDerivAt_pow 4 x
  have hdp : ∀ x ∈ Ioo (min (0:ℝ) 1) (max 0 1), 0 ≤ 4*x^3 := by
    intro x hx
    norm_num at hx
    exact mul_nonneg (by norm_num) (pow_nonneg hx.1.le _)
  have hiff := integrable_comp_mul_deriv_iff_of_deriv_nonneg (g := betaKernel) hf hd hdp
  have hsub : IntervalIntegrable (fun x : ℝ => betaKernel (x^4)*(4*x^3)) volume 0 1 := by
    apply hiff.mpr
    simpa using betaKernel_integrable
  have heq : EqOn (fun x : ℝ => betaKernel (x^4)*(4*x^3))
      (fun x : ℝ => 4*(1/Real.sqrt (1-x^4))) (uIoo 0 1) := by
    intro x hx
    have hx' : x ∈ Ioo (0:ℝ) 1 := by simpa only [uIoo_of_le (by norm_num : (0:ℝ)≤1)] using hx
    exact substitution_kernel x hx'.1 hx'.2
  have hscaled := hsub.congr_uIoo heq
  have hF : IntervalIntegrable (fun x : ℝ => 1/Real.sqrt (1-x^4)) volume 0 1 := by
    have h := hscaled.const_mul (1/4:ℝ)
    simpa only [← mul_assoc,show (1/4:ℝ)*4 = 1 by norm_num,one_mul] using h
  refine ⟨hF,?_⟩
  have hchange := integral_comp_mul_deriv_of_deriv_nonneg (g := betaKernel) hf hd hdp
  have heval : (∫ x : ℝ in (0:ℝ)..1, betaKernel (x^4)*(4*x^3)) =
      4*(∫ x : ℝ in (0:ℝ)..1, 1/Real.sqrt (1-x^4)) := by
    rw [integral_congr_uIoo heq,intervalIntegral.integral_const_mul]
  simp only [Function.comp_apply] at hchange
  norm_num at hchange
  rw [heval] at hchange
  rw [integral_betaKernel] at hchange
  have hG3 : 0 < Real.Gamma (3/4) := Real.Gamma_pos_of_pos (by norm_num)
  have hs2 : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  have hspi : 0 < Real.sqrt Real.pi := Real.sqrt_pos.mpr Real.pi_pos
  have hratio : Real.Gamma (1/4)*Real.sqrt Real.pi/Real.Gamma (3/4) =
      Real.Gamma (1/4)^2/(Real.sqrt 2*Real.sqrt Real.pi) := by
    apply (div_eq_div_iff (ne_of_gt hG3) (mul_ne_zero (ne_of_gt hs2) (ne_of_gt hspi))).mpr
    calc
      _ = Real.Gamma (1/4)*Real.sqrt 2*(Real.sqrt Real.pi)^2 := by ring
      _ = Real.Gamma (1/4)*Real.sqrt 2*Real.pi := by rw [Real.sq_sqrt Real.pi_pos.le]
      _ = Real.Gamma (1/4)*(Real.pi*Real.sqrt 2) := by ring
      _ = Real.Gamma (1/4)*(Real.Gamma (1/4)*Real.Gamma (3/4)) := by rw [Elementary.gammaReflection]
      _ = _ := by ring
  rw [hratio] at hchange
  have hv : (∫ x : ℝ in (0:ℝ)..1, 1/Real.sqrt (1-x^4)) =
      (Real.Gamma (1/4)^2/(Real.sqrt 2*Real.sqrt Real.pi))/4 := by linarith
  rw [Real.sqrt_mul (by norm_num : (0:ℝ)≤2)]
  simpa only [div_div,mul_comm,mul_left_comm,mul_assoc] using hv

end Plouffe.Proofs.Gamma
