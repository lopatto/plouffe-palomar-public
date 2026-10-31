/-
Copyright (c) 2026 Patrick Lopatto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Lopatto
-/
module

public import Plouffe.Proofs.EtaLog
public import Plouffe.Proofs.EtaRatio

public section
namespace Plouffe.Proofs.Endpoint

/-- The exponent-one inversion relation from eta inversion at 2i. -/
theorem s1Inversion : Contracts.s1Inversion := by
  have h1 := EtaLog.etaLog 1 (by norm_num)
  have h4 := EtaLog.etaLog 4 (by norm_num)
  norm_num at h1 h4
  have hi := EtaRatio.log_norm_eta_inverse (2*Complex.I) (by norm_num [Complex.mul_im])
  have hinv : (-1:ℂ)/(2*Complex.I) = (1/2:ℂ)*Complex.I := by
    norm_num [div_eq_mul_inv,mul_inv_rev,Complex.inv_I]
    ring
  rw [hinv] at hi
  norm_num only [norm_mul,Complex.norm_ofNat,Complex.norm_I,mul_one] at hi
  change S 1 1 = S 1 4-(1/2:ℝ)*Real.log 2+Real.pi/8
  linarith

/-- The exponent-one doubling difference from the exact positive eta ratio. -/
theorem s4Difference : Contracts.s4Difference := by
  have h2 := EtaLog.etaLog 2 (by norm_num)
  have h4 := EtaLog.etaLog 4 (by norm_num)
  norm_num at h2 h4
  have hpC : 0 < ‖ModularForm.eta (2*Complex.I)‖ :=
    norm_pos_iff.mpr (ModularForm.eta_ne_zero (by norm_num [Complex.mul_im]))
  have hpD : 0 < ‖ModularForm.eta Complex.I‖ :=
    norm_pos_iff.mpr (ModularForm.eta_ne_zero (by norm_num))
  have hr := EtaRatio.etaRatio
  unfold Contracts.etaRatio at hr
  have hl : Real.log ‖ModularForm.eta (2*Complex.I)‖-Real.log ‖ModularForm.eta Complex.I‖ =
      (-(3:ℝ)/8)*Real.log 2 := by
    simpa only [Real.log_div (ne_of_gt hpC) (ne_of_gt hpD),Real.rpow_eq_pow,
      Real.log_rpow (show (0:ℝ)<2 by norm_num)] using congrArg Real.log hr
  change S 1 4-S 1 2 = (3/8:ℝ)*Real.log 2-Real.pi/12
  linarith


end Plouffe.Proofs.Endpoint
