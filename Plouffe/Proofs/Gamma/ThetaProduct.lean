/-
Copyright (c) 2026 Patrick Lopatto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Lopatto
-/
module

public import Plouffe.Proofs.Gamma.ThetaProduct.Euler
public import Plouffe.Proofs.Gamma.ThetaProduct.Bridge
public import Plouffe.Proofs.Gamma.Theta
public import Plouffe.Proofs.EtaRatio.Modular
public import Mathlib.Tactic.Linarith

public section
namespace Plouffe.Proofs.Gamma.ThetaProduct

private theorem qParam_imaginary (y : ℝ) :
    Function.Periodic.qParam 1 ((y:ℂ)*Complex.I) = (Real.exp (-2*Real.pi*y):ℂ) := by
  unfold Function.Periodic.qParam
  norm_num only [Complex.ofReal_one,div_one]
  rw [Complex.ofReal_exp]
  congr 1
  push_cast
  ring_nf
  simp [Complex.I_sq]

/-- The convergent Jacobi Euler product at the self-dual nome equals the eta side.
This is solely a product identity; it does not assume or assert a theta-series/product theorem. -/
theorem jacobi_euler_product_at_I :
    (∏' j : ℕ, (1-Real.exp (-Real.pi)^(2*(j+1)))*(1+Real.exp (-Real.pi)^(2*j+1))^2) =
      Real.sqrt 2*‖ModularForm.eta Complex.I‖ := by
  let q := Real.exp (-Real.pi)
  let B := ‖ModularForm.eta ((1+Complex.I)/2)‖
  let D := ‖ModularForm.eta Complex.I‖
  have hq : |q| < 1 := by
    rw [abs_of_pos (Real.exp_pos _)]
    exact Real.exp_lt_one_iff.mpr (neg_lt_zero.mpr Real.pi_pos)
  have hq2 : |q^2| < 1 := by
    rw [abs_pow]
    exact pow_lt_one₀ (abs_nonneg q) hq (by norm_num)
  have hP : 0 < EtaRatio.euler (-q) := EtaRatio.euler_pos (-q) (by simpa using hq)
  have hQ : 0 < EtaRatio.euler (q^2) := EtaRatio.euler_pos (q^2) hq2
  have hqpow : q^2 = Real.exp (-2*Real.pi) := by
    dsimp [q]
    rw [← Real.exp_nat_mul]
    congr 1
    push_cast
    ring
  have hparamB : Function.Periodic.qParam 1 ((1+Complex.I)/2) = ((-q:ℝ):ℂ) := by
    unfold Function.Periodic.qParam
    norm_num only [Complex.ofReal_one,div_one]
    have he : 2*(Real.pi:ℂ)*Complex.I*((1+Complex.I)/2) = -(Real.pi:ℂ)+(Real.pi:ℂ)*Complex.I := by
      ring_nf
      simp [Complex.I_sq]
      ring
    rw [he,Complex.exp_add,Complex.exp_pi_mul_I,mul_neg_one]
    dsimp [q]
    push_cast
    rfl
  have hparamD : Function.Periodic.qParam 1 Complex.I = ((q^2:ℝ):ℂ) := by
    rw [hqpow]
    simpa only [Complex.ofReal_one,one_mul,mul_one] using qParam_imaginary 1
  have hB : B = Real.exp (-Real.pi/24)*EtaRatio.euler (-q) := by
    have h := EtaRatio.norm_eta_q ((1+Complex.I)/2) (-q) (by simpa using hq) hparamB
    convert h using 2
    congr 1
    norm_num [Complex.div_im,Complex.normSq]
    ring
  have hD : D = Real.exp (-Real.pi/12)*EtaRatio.euler (q^2) := by
    simpa only [Complex.I_im,mul_one] using EtaRatio.norm_eta_q Complex.I (q^2) hq2 hparamD
  have hBp : 0 < B := norm_pos_iff.mpr (ModularForm.eta_ne_zero (by norm_num [Complex.div_im,Complex.normSq]))
  have hDp : 0 < D := norm_pos_iff.mpr (ModularForm.eta_ne_zero (by norm_num))
  have hLB : Real.log B = -Real.pi/24+Real.log (EtaRatio.euler (-q)) := by
    rw [hB,Real.log_mul (Real.exp_ne_zero _) (ne_of_gt hP),Real.log_exp]
  have hLD : Real.log D = -Real.pi/12+Real.log (EtaRatio.euler (q^2)) := by
    rw [hD,Real.log_mul (Real.exp_ne_zero _) (ne_of_gt hQ),Real.log_exp]
  let w : ℂ := (1+Complex.I)/2
  have hwp : 0 < w.im := by dsimp [w]; norm_num [Complex.div_im,Complex.normSq]
  have hiB := EtaRatio.log_norm_eta_inverse w hwp
  have hinvB : (-1:ℂ)/w = Complex.I-1 := by
    dsimp [w]
    apply (div_eq_iff (by intro h; have := congrArg Complex.im h; norm_num [Complex.div_im,Complex.normSq] at this)).mpr
    ring_nf
    norm_num [Complex.I_sq]
  have hshift : ‖ModularForm.eta (Complex.I-1)‖ = D := by
    simpa only [sub_add_cancel] using (EtaRatio.norm_eta_add_one (Complex.I-1)).symm
  have hnormw : ‖w‖ = Real.sqrt (1/2) := by
    dsimp [w]
    norm_num [Complex.norm_def,Complex.normSq,Complex.div_re,Complex.div_im]
    have hs0 : Real.sqrt 2 ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr (by norm_num))
    field_simp
    nlinarith [Real.sq_sqrt (show (0:ℝ)≤2 by norm_num)]
  rw [hinvB,hshift,hnormw,Real.log_sqrt (by norm_num),Real.log_div (by norm_num) (by norm_num),Real.log_one] at hiB
  change Real.log D = (1/2)*((0-Real.log 2)/2)+Real.log B at hiB
  change (∏' j : ℕ, (1-q^(2*(j+1)))*(1+q^(2*j+1))^2) = Real.sqrt 2*D
  rw [jacobi_product_eq_euler q hq]
  apply Real.log_injOn_pos (div_pos (pow_pos hP _) hQ) (mul_pos (Real.sqrt_pos.mpr (by norm_num)) hDp)
  rw [Real.log_div (pow_ne_zero _ (ne_of_gt hP)) (ne_of_gt hQ),Real.log_pow,
    Real.log_mul (ne_of_gt (Real.sqrt_pos.mpr (by norm_num))) (ne_of_gt hDp),Real.log_sqrt (by norm_num)]
  norm_num only [Nat.cast_ofNat]
  linarith

/-- The native theta Gaussian series equals the now-proved convergent Jacobi product. -/
theorem theta_I_eq_jacobi_product :
    (jacobiTheta Complex.I).re =
      (∏' j : ℕ, (1-Real.exp (-Real.pi)^(2*(j+1)))*(1+Real.exp (-Real.pi)^(2*j+1))^2) := by
  rw [jacobi_product_eq_gaussian (Real.exp (-Real.pi)) (Real.exp_pos _)
    (Real.exp_lt_one_iff.mpr (neg_lt_zero.mpr Real.pi_pos))]
  have h := congrArg Complex.re Plouffe.Proofs.Gamma.theta_I_eq_real_gaussian
  simp only [Complex.ofReal_re] at h
  rw [h]
  congr 2
  apply tsum_congr
  intro j
  rw [← Real.exp_nat_mul]
  congr 1
  push_cast
  ring

/-- Exact eta/theta normalization at the square lattice, with no singular value assumed. -/
theorem theta_I_eq_eta :
    (jacobiTheta Complex.I).re = Real.sqrt 2*‖ModularForm.eta Complex.I‖ :=
  theta_I_eq_jacobi_product.trans jacobi_euler_product_at_I

/-- The supporting eta/theta obligation in its exact frozen orientation. -/
theorem etaTheta :
    ‖ModularForm.eta Complex.I‖ = (jacobiTheta Complex.I).re/Real.sqrt 2 := by
  rw [theta_I_eq_eta]
  have hs : Real.sqrt 2 ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr (by norm_num))
  field_simp

end Plouffe.Proofs.Gamma.ThetaProduct
