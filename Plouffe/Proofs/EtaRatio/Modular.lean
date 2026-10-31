/-
Copyright (c) 2026 Patrick Lopatto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Lopatto
-/
module

public import Plouffe.Proofs.EtaRatio.Euler
public import Mathlib.NumberTheory.ModularForms.Discriminant
public import Mathlib.Topology.Algebra.InfiniteSum.Field
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

public section
namespace Plouffe.Proofs.EtaRatio

/-- Norm of eta when its q-parameter is real and belongs to the open unit interval. -/
theorem norm_eta_q (z : ℂ) (q : ℝ) (hq : |q| < 1)
    (hparam : Function.Periodic.qParam 1 z = (q:ℂ)) :
    ‖ModularForm.eta z‖ = Real.exp (-Real.pi*z.im/12)*euler q := by
  have hqnorm : ‖(q:ℂ)‖ < 1 := by simpa [Complex.norm_real,Real.norm_eq_abs] using hq
  have hQ (m : ℕ) : ModularForm.eta_q m z = ((q^(m+1):ℝ):ℂ) := by
    simp only [ModularForm.eta_q,hparam,Complex.ofReal_pow]
  have hmult : Multipliable (fun m : ℕ => 1-ModularForm.eta_q m z) := by
    simpa only [hQ,Complex.ofReal_pow] using ModularForm.multipliable_one_sub_pow hqnorm
  rw [ModularForm.eta,norm_mul,Function.Periodic.norm_qParam,hmult.norm_tprod]
  congr 1
  · congr 1
    ring
  · unfold euler
    apply tprod_congr
    intro m
    rw [hQ,← Complex.ofReal_one,← Complex.ofReal_sub,Complex.norm_real,Real.norm_eq_abs]
    apply abs_of_pos
    have hp : |q^(m+1)| < 1 := by rw [abs_pow]; exact pow_lt_one₀ (abs_nonneg q) hq (Nat.succ_ne_zero m)
    exact sub_pos.mpr ((le_abs_self _).trans_lt hp)

/-- Unit translation leaves the eta norm invariant, with no phase choice. -/
theorem norm_eta_add_one (z : ℂ) : ‖ModularForm.eta (z+1)‖ = ‖ModularForm.eta z‖ := by
  have hparam : Function.Periodic.qParam 1 (z+1) = Function.Periodic.qParam 1 z := by
    unfold Function.Periodic.qParam
    norm_num only [Complex.ofReal_one,div_one]
    rw [show 2*(Real.pi:ℂ)*Complex.I*(z+1) = 2*(Real.pi:ℂ)*Complex.I*z+2*(Real.pi:ℂ)*Complex.I by ring,
      Complex.exp_add,Complex.exp_two_pi_mul_I,mul_one]
  have hQ (m : ℕ) : ModularForm.eta_q m (z+1) = ModularForm.eta_q m z := by
    simp only [ModularForm.eta_q,hparam]
  rw [ModularForm.eta,ModularForm.eta,norm_mul,norm_mul,Function.Periodic.norm_qParam,
    Function.Periodic.norm_qParam]
  simp only [Complex.add_im,Complex.one_im,add_zero]
  congr 1
  congr 1
  exact tprod_congr (fun m => by rw [hQ])

/-- Eta inversion in norm, with the square-root magnitude fixed canonically. -/
theorem norm_eta_inverse (z : ℂ) (hz : 0 < z.im) :
    ‖ModularForm.eta (-1/z)‖ = Real.rpow ‖z‖ (1/2)*‖ModularForm.eta z‖ := by
  have h := ModularForm.eta_comp_eq_csqrt_I_inv hz
  change ModularForm.eta (-1/z) = (Complex.sqrt Complex.I)⁻¹*(Complex.sqrt z*ModularForm.eta z) at h
  have hn := congrArg (fun w : ℂ => ‖w‖) h
  have hI : ‖Complex.sqrt Complex.I‖ = 1 := by
    simpa only [Complex.sqrt,Nat.cast_ofNat,Complex.norm_I,Real.one_rpow] using Complex.norm_cpow_inv_nat Complex.I 2
  have hZ : ‖Complex.sqrt z‖ = ‖z‖^((2:ℝ)⁻¹) := by
    simpa only [Complex.sqrt,Nat.cast_ofNat] using Complex.norm_cpow_inv_nat z 2
  rw [norm_mul,norm_inv,hI,norm_mul,hZ,inv_one,one_mul] at hn
  simpa only [Real.rpow_eq_pow,one_div] using hn

/-- Logarithmic eta inversion, justified by positive norms on the upper half-plane. -/
theorem log_norm_eta_inverse (z : ℂ) (hz : 0 < z.im) :
    Real.log ‖ModularForm.eta (-1/z)‖ = (1/2)*Real.log ‖z‖+Real.log ‖ModularForm.eta z‖ := by
  have hz0 : z ≠ 0 := by
    intro h
    rw [h,Complex.zero_im] at hz
    exact lt_irrefl 0 hz
  rw [norm_eta_inverse z hz,Real.rpow_eq_pow,Real.log_mul (ne_of_gt (Real.rpow_pos_of_pos (norm_pos_iff.mpr hz0) _))
    (norm_ne_zero_iff.mpr (ModularForm.eta_ne_zero hz)),Real.log_rpow (norm_pos_iff.mpr hz0)]


end Plouffe.Proofs.EtaRatio
