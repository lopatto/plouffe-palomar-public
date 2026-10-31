/-
Copyright (c) 2026 Patrick Lopatto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Lopatto
-/
module

public import Plouffe.Proofs.Gamma.Evaluation
public import Plouffe.Proofs.Endpoint

public section
namespace Plouffe.Proofs.GammaEndpoints

private theorem log_eta_I_of (hEval : Contracts.etaGamma) :
    Real.log ‖ModularForm.eta Complex.I‖ = Real.log (Real.Gamma (1/4))-Real.log 2-(3/4)*Real.log Real.pi := by
  have hG : 0 < Real.Gamma (1/4) := Real.Gamma_pos_of_pos (by norm_num)
  have hP : 0 < Real.rpow Real.pi (3/4) := Real.rpow_pos_of_pos Real.pi_pos _
  rw [hEval,Real.log_div hG.ne' (mul_ne_zero (by norm_num) hP.ne'),
    Real.log_mul (by norm_num : (2:ℝ) ≠ 0) hP.ne',Real.rpow_eq_pow,Real.log_rpow Real.pi_pos]
  ring

/-- Endpoint scalar reduction using the independently proved singular-value input. -/
theorem gammaS2_of_etaGamma (hEval : Contracts.etaGamma) : Contracts.gammaS2 := by
  have h2 := EtaLog.etaLog 2 (by norm_num)
  norm_num at h2
  have hl := log_eta_I_of hEval
  have hG1 : 0 < Real.Gamma (1/4) := Real.Gamma_pos_of_pos (by norm_num)
  have hG3 : 0 < Real.Gamma (3/4) := Real.Gamma_pos_of_pos (by norm_num)
  have hroot : 0 < Real.sqrt 2 := by positivity
  have href := congrArg Real.log Elementary.gammaReflection
  rw [Real.log_mul hG1.ne' hG3.ne',Real.log_mul Real.pi_pos.ne' hroot.ne',
    Real.log_sqrt (by norm_num : (0:ℝ) ≤ 2)] at href
  change S 1 2 = (1/4:ℝ)*Real.log (4/Real.pi)-Real.pi/12+Real.log (Real.Gamma (3/4))
  rw [Real.log_div (by norm_num : (4:ℝ) ≠ 0) Real.pi_pos.ne']
  have h4 : Real.log (4:ℝ) = 2*Real.log 2 := by
    rw [show (4:ℝ) = 2^2 by norm_num,Real.log_pow]
    norm_num
  rw [h4]
  linarith

/-- The c²=4 Gamma normalization from the exponent-one doubling relation. -/
theorem gammaS4_of_etaGamma (hEval : Contracts.etaGamma) : Contracts.gammaS4 := by
  have h2 := EtaLog.etaLog 2 (by norm_num)
  norm_num at h2
  have hl := log_eta_I_of hEval
  have hd := Endpoint.s4Difference
  change S 1 4-S 1 2 = (3/8:ℝ)*Real.log 2-Real.pi/12 at hd
  change S 1 4 = -(1/6:ℝ)*Real.log (Real.rpow 2 (-(33:ℝ)/4))+
    (1/6:ℝ)*Real.log (Real.rpow Real.pi ((9:ℝ)/2))-Real.log (Real.Gamma (1/4))-Real.pi/6
  rw [Real.rpow_eq_pow,Real.rpow_eq_pow,Real.log_rpow (by norm_num : (0:ℝ)<2),Real.log_rpow Real.pi_pos]
  linarith

/-- The paper's quarter-Gamma evaluation at series parameter r=2. -/
theorem gammaS2 : Contracts.gammaS2 := gammaS2_of_etaGamma Gamma.etaGamma

/-- The paper's quarter-Gamma evaluation at series parameter r=4. -/
theorem gammaS4 : Contracts.gammaS4 := gammaS4_of_etaGamma Gamma.etaGamma

#print axioms gammaS2
#print axioms gammaS4
#print axioms gammaS2_of_etaGamma
#print axioms gammaS4_of_etaGamma

end Plouffe.Proofs.GammaEndpoints
