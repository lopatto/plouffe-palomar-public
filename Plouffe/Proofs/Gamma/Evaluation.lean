/-
Copyright (c) 2026 Patrick Lopatto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Lopatto
-/
module

public import Plouffe.Contracts
public import Plouffe.Proofs.Gamma.ThetaAGM.Link
public import Plouffe.Proofs.Gamma.AGMIntegral
public import Plouffe.Proofs.Gamma.Lemniscate
public import Plouffe.Proofs.Gamma.ThetaProduct

public section
namespace Plouffe.Proofs.Gamma

/-- Admission-free scalar assembly; the sole explicit input is the independent theta/product bridge. -/
theorem etaGamma_of_theta
    (htheta : (jacobiTheta Complex.I).re = Real.sqrt 2*‖ModularForm.eta Complex.I‖) :
    Contracts.etaGamma := by
  let M : ℝ := (NNReal.agm (1:NNReal) (NNReal.mk (1/Real.sqrt 2) (by positivity)):ℝ)
  have hMt : M*(jacobiTheta Complex.I).re^2 = 1 := ThetaAGM.theta_agm
  have hJ := lemniscatic_integral
  have hMJ := agm_lemniscatic hJ.1
  rw [hJ.2] at hMJ
  change M*(Real.Gamma (1/4)^2/(4*Real.sqrt (2*Real.pi))) = Real.pi/(2*Real.sqrt 2) at hMJ
  have hs2 : 0 < Real.sqrt 2 := by positivity
  have hspi : 0 < Real.sqrt Real.pi := by positivity
  have hs2sq : (Real.sqrt 2)^2 = 2 := Real.sq_sqrt (by norm_num)
  have hMG : M*Real.Gamma (1/4)^2 = 2*Real.pi*Real.sqrt Real.pi := by
    calc
      _ = (M*(Real.Gamma (1/4)^2/(4*Real.sqrt (2*Real.pi))))*(4*Real.sqrt (2*Real.pi)) := by
        field_simp
      _ = (Real.pi/(2*Real.sqrt 2))*(4*Real.sqrt (2*Real.pi)) := by rw [hMJ]
      _ = _ := by
        rw [Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 2)]
        field_simp
        ring
  have hG : Real.Gamma (1/4)^2 = 4*Real.pi*Real.sqrt Real.pi*‖ModularForm.eta Complex.I‖^2 := by
    calc
      _ = (M*(jacobiTheta Complex.I).re^2)*Real.Gamma (1/4)^2 := by rw [hMt]; ring
      _ = (M*Real.Gamma (1/4)^2)*(jacobiTheta Complex.I).re^2 := by ring
      _ = _ := by rw [hMG,htheta,mul_pow,hs2sq]; ring
  have hR : (Real.rpow Real.pi (3/4))^2 = Real.pi*Real.sqrt Real.pi := by
    rw [Real.rpow_eq_pow]
    rw [← Real.rpow_mul_natCast Real.pi_pos.le,show (3/4:ℝ)*(2:ℕ) = 1+1/2 by norm_num,
      Real.rpow_add Real.pi_pos,Real.rpow_one,← Real.sqrt_eq_rpow]
  have hRp : 0 < Real.rpow Real.pi (3/4) := Real.rpow_pos_of_pos Real.pi_pos _
  have hGp : 0 < Real.Gamma (1/4) := Real.Gamma_pos_of_pos (by norm_num)
  have hsq : (‖ModularForm.eta Complex.I‖*(2*Real.rpow Real.pi (3/4)))^2 = Real.Gamma (1/4)^2 := by
    rw [mul_pow,mul_pow,hR]
    nlinarith [hG]
  have heq : ‖ModularForm.eta Complex.I‖*(2*Real.rpow Real.pi (3/4)) = Real.Gamma (1/4) := by
    nlinarith [mul_nonneg (norm_nonneg (ModularForm.eta Complex.I)) (mul_pos (by norm_num : (0:ℝ)<2) hRp).le]
  exact (eq_div_iff (mul_ne_zero (by norm_num) hRp.ne')).mpr heq

/-- The original endpoint singular value, using the independent theta/product theorem. -/
theorem etaGamma : Contracts.etaGamma := etaGamma_of_theta ThetaProduct.theta_I_eq_eta

#print axioms etaGamma_of_theta
#print axioms etaGamma

end Plouffe.Proofs.Gamma
