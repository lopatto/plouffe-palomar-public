/-
Copyright (c) 2026 Patrick Lopatto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Lopatto
-/
module

public import Plouffe.Contracts
public import Plouffe.Proofs.EtaRatio.Modular
public import Mathlib.Tactic.Linarith

public section
namespace Plouffe.Proofs.EtaRatio

private theorem qParam_imaginary (y : ℝ) :
    Function.Periodic.qParam 1 ((y:ℂ)*Complex.I) = (Real.exp (-2*Real.pi*y):ℂ) := by
  unfold Function.Periodic.qParam
  norm_num only [Complex.ofReal_one,div_one]
  rw [Complex.ofReal_exp]
  congr 1
  push_cast
  ring_nf
  simp [Complex.I_sq]

private theorem norm_eta_imaginary (y : ℝ) (hy : 0 < y) :
    ‖ModularForm.eta ((y:ℂ)*Complex.I)‖ =
      Real.exp (-Real.pi*y/12)*euler (Real.exp (-2*Real.pi*y)) := by
  have hq : |Real.exp (-2*Real.pi*y)| < 1 := by
    rw [abs_of_pos (Real.exp_pos _)]
    apply Real.exp_lt_one_iff.mpr
    nlinarith [Real.pi_pos]
  have h := norm_eta_q ((y:ℂ)*Complex.I) (Real.exp (-2*Real.pi*y)) hq (qParam_imaginary y)
  simpa only [Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im,Complex.I_im,Complex.I_re,
    mul_one,mul_zero,add_zero] using h

private theorem norm_eta_half_shift :
    ‖ModularForm.eta ((1+Complex.I)/2)‖ = Real.exp (-Real.pi/24)*euler (-Real.exp (-Real.pi)) := by
  have hq : |-Real.exp (-Real.pi)| < 1 := by
    rw [abs_neg,abs_of_pos (Real.exp_pos _)]
    exact Real.exp_lt_one_iff.mpr (neg_lt_zero.mpr Real.pi_pos)
  have hparam : Function.Periodic.qParam 1 ((1+Complex.I)/2) = (-Real.exp (-Real.pi):ℝ) := by
    unfold Function.Periodic.qParam
    norm_num only [Complex.ofReal_one,div_one]
    have he : 2*(Real.pi:ℂ)*Complex.I*((1+Complex.I)/2) = -(Real.pi:ℂ)+(Real.pi:ℂ)*Complex.I := by
      ring_nf
      simp [Complex.I_sq]
      ring
    rw [he,Complex.exp_add,Complex.exp_pi_mul_I,mul_neg_one]
    push_cast
    rfl
  have h := norm_eta_q ((1+Complex.I)/2) (-Real.exp (-Real.pi)) hq hparam
  convert h using 2
  congr 1
  norm_num [Complex.div_im,Complex.normSq]
  ring

/-- The independent endpoint eta ratio, with positivity fixing every real logarithm and root. -/
theorem etaRatio : Contracts.etaRatio := by
  let A := ‖ModularForm.eta ((1/2:ℂ)*Complex.I)‖
  let B := ‖ModularForm.eta ((1+Complex.I)/2)‖
  let C := ‖ModularForm.eta (2*Complex.I)‖
  let D := ‖ModularForm.eta Complex.I‖
  let q := Real.exp (-Real.pi)
  have hq : |q| < 1 := by
    rw [abs_of_pos (Real.exp_pos _)]
    exact Real.exp_lt_one_iff.mpr (neg_lt_zero.mpr Real.pi_pos)
  have hq2 : q^2 = Real.exp (-2*Real.pi) := by
    dsimp [q]
    rw [← Real.exp_nat_mul]
    congr 1
    push_cast
    ring
  have hq4 : q^4 = Real.exp (-4*Real.pi) := by
    dsimp [q]
    rw [← Real.exp_nat_mul]
    congr 1
    push_cast
    ring
  have hA : A = Real.exp (-Real.pi/24)*euler q := by
    have h := norm_eta_imaginary (1/2) (by norm_num)
    push_cast at h
    rw [show -Real.pi*(1/2)/12 = -Real.pi/24 by ring,
      show -2*Real.pi*(1/2) = -Real.pi by ring] at h
    exact h
  have hB : B = Real.exp (-Real.pi/24)*euler (-q) := norm_eta_half_shift
  have hC : C = Real.exp (-Real.pi/6)*euler (q^4) := by
    rw [hq4]
    have h := norm_eta_imaginary 2 (by norm_num)
    push_cast at h
    rw [show -Real.pi*2/12 = -Real.pi/6 by ring,
      show -2*Real.pi*2 = -4*Real.pi by ring] at h
    exact h
  have hD : D = Real.exp (-Real.pi/12)*euler (q^2) := by
    rw [hq2]
    simpa only [Complex.ofReal_one,one_mul,mul_one] using norm_eta_imaginary 1 (by norm_num)
  have hprod : A*B*C = D^3 := by
    rw [hA,hB,hC,hD]
    have he : Real.exp (-Real.pi/24)*Real.exp (-Real.pi/24)*Real.exp (-Real.pi/6) =
        (Real.exp (-Real.pi/12))^3 := by
      rw [← Real.exp_add,← Real.exp_add,← Real.exp_nat_mul]
      congr 1
      push_cast
      ring
    calc
      _ = (Real.exp (-Real.pi/24)*Real.exp (-Real.pi/24)*Real.exp (-Real.pi/6))*
          (euler q*euler (-q)*euler (q^4)) := by ring
      _ = _ := by rw [he,euler_duplication q hq]; ring
  have hAp : 0 < A := norm_pos_iff.mpr (ModularForm.eta_ne_zero (by norm_num [Complex.mul_im,Complex.div_re,Complex.normSq]))
  have hBp : 0 < B := norm_pos_iff.mpr (ModularForm.eta_ne_zero (by norm_num [Complex.div_im,Complex.normSq]))
  have hCp : 0 < C := norm_pos_iff.mpr (ModularForm.eta_ne_zero (by norm_num [Complex.mul_im]))
  have hDp : 0 < D := norm_pos_iff.mpr (ModularForm.eta_ne_zero (by norm_num))
  have hlogs := congrArg Real.log hprod
  rw [Real.log_mul (mul_ne_zero (ne_of_gt hAp) (ne_of_gt hBp)) (ne_of_gt hCp),
    Real.log_mul (ne_of_gt hAp) (ne_of_gt hBp),Real.log_pow] at hlogs
  norm_num only [Nat.cast_ofNat] at hlogs
  have hiA := log_norm_eta_inverse (2*Complex.I) (by norm_num [Complex.mul_im])
  have hinvA : (-1:ℂ)/(2*Complex.I) = (1/2:ℂ)*Complex.I := by
    norm_num [div_eq_mul_inv,mul_inv_rev,Complex.inv_I]
    ring
  rw [hinvA] at hiA
  norm_num only [norm_mul,Complex.norm_ofNat,Complex.norm_I,mul_one] at hiA
  change Real.log A = (1/2)*Real.log 2+Real.log C at hiA
  let w : ℂ := (1+Complex.I)/2
  have hwp : 0 < w.im := by dsimp [w]; norm_num [Complex.div_im,Complex.normSq]
  have hiB := log_norm_eta_inverse w hwp
  have hinvB : (-1:ℂ)/w = Complex.I-1 := by
    dsimp [w]
    apply (div_eq_iff (by intro h; have := congrArg Complex.im h; norm_num [Complex.div_im,Complex.normSq] at this)).mpr
    ring_nf
    norm_num [Complex.I_sq]
  rw [hinvB] at hiB
  have hshift : ‖ModularForm.eta (Complex.I-1)‖ = D := by
    simpa only [sub_add_cancel] using (norm_eta_add_one (Complex.I-1)).symm
  have hnormw : ‖w‖ = Real.sqrt (1/2) := by
    dsimp [w]
    norm_num [Complex.norm_def,Complex.normSq,Complex.div_re,Complex.div_im]
    have hs0 : Real.sqrt 2 ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr (by norm_num))
    field_simp
    nlinarith [Real.sq_sqrt (show (0:ℝ)≤2 by norm_num)]
  rw [hshift,hnormw,Real.log_sqrt (by norm_num),Real.log_div (by norm_num) (by norm_num),Real.log_one] at hiB
  change Real.log D = (1/2)*((0-Real.log 2)/2)+Real.log B at hiB
  change C/D = Real.rpow 2 (-(3:ℝ)/8)
  apply Real.log_injOn_pos (div_pos hCp hDp) (Real.rpow_pos_of_pos (by norm_num) _)
  rw [Real.log_div (ne_of_gt hCp) (ne_of_gt hDp),Real.log_rpow (by norm_num)]
  linarith


end Plouffe.Proofs.EtaRatio
