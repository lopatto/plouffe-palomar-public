/-
Copyright (c) 2026 Patrick Lopatto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Lopatto
-/
module

public import Mathlib.Analysis.SpecialFunctions.Gamma.Beta

public section
namespace Plouffe.Proofs.Gamma

/-- The beta/Gamma side of the lemniscatic quarter-argument evaluation. -/
theorem beta_quarter_half :
    Complex.betaIntegral (1/4) (1/2) =
      ((Real.Gamma (1/4)*Real.sqrt Real.pi/Real.Gamma (3/4):ℝ):ℂ) := by
  rw [Complex.betaIntegral_eq_Gamma_mul_div (1/4) (1/2) (by norm_num) (by norm_num)]
  norm_num only [show (1/4:ℂ)+(1/2:ℂ) = (3/4:ℂ) by norm_num]
  have h1 : (1/4:ℂ) = ((1/4:ℝ):ℂ) := by norm_num
  have h3 : (3/4:ℂ) = ((3/4:ℝ):ℂ) := by norm_num
  have h2 : (1/2:ℂ) = ((1/2:ℝ):ℂ) := by norm_num
  rw [h1,h3,h2]
  simp only [Complex.Gamma_ofReal,Real.Gamma_one_half_eq]
  push_cast
  rfl


end Plouffe.Proofs.Gamma
