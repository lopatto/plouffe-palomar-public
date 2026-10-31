/-
Copyright (c) 2026 Patrick Lopatto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Lopatto
-/
module

public import Plouffe.Proofs.Series
public import Plouffe.Contracts
public import Plouffe.Proofs.EtaLog.Lambert
public import Mathlib.Topology.Algebra.InfiniteSum.Field

public section
namespace Plouffe.Proofs.EtaLog

private theorem eta_q_imaginary (r : ℝ) (m : ℕ) :
    ModularForm.eta_q m ((r/2:ℂ)*Complex.I) = (Real.exp (-Real.pi*r)^(m+1):ℂ) := by
  rw [ModularForm.eta_q_eq_pow]
  push_cast
  congr 1
  congr 1
  ring_nf
  simp [Complex.I_sq]

private theorem S_one_lambert (r : ℝ) (hr : 0 < r) :
    S 1 r = ∑' j : ℕ, Real.exp (-Real.pi*r)^(j+1)/
      (((j+1:ℕ):ℝ)*(1-Real.exp (-Real.pi*r)^(j+1))) := by
  have hsum := Series.summableS 1 r hr
  unfold S
  apply tsum_congr
  intro j
  have hq : Real.exp (-Real.pi*r)^(j+1) = (Real.exp (Real.pi*r*((j+1:ℕ):ℝ)))⁻¹ := by
    rw [← Real.exp_nat_mul,show ((j+1:ℕ):ℝ)*(-Real.pi*r) = -(Real.pi*r*((j+1:ℕ):ℝ)) by ring,Real.exp_neg]
  rw [hq,pow_one]
  have hx0 : Real.exp (Real.pi*r*((j+1:ℕ):ℝ)) ≠ 0 := Real.exp_ne_zero _
  have hx1 : Real.exp (Real.pi*r*((j+1:ℕ):ℝ))-1 ≠ 0 := ne_of_gt (sub_pos.mpr
    (Real.one_lt_exp_iff.mpr (mul_pos (mul_pos Real.pi_pos hr) (by positivity))))
  have hk : ((j+1:ℕ):ℝ) ≠ 0 := by positivity
  field_simp

private theorem eta_norm_product (r : ℝ) (hr : 0 < r) :
    ‖ModularForm.eta ((r/2:ℂ)*Complex.I)‖ = Real.exp (-Real.pi*r/24)*
      ∏' m : ℕ, (1-Real.exp (-Real.pi*r)^(m+1)) := by
  have hq0 : 0 < Real.exp (-Real.pi*r) := Real.exp_pos _
  have hq1 : Real.exp (-Real.pi*r) < 1 := Real.exp_lt_one_iff.mpr (by nlinarith [Real.pi_pos])
  have hqnorm : ‖(Real.exp (-Real.pi*r):ℂ)‖ < 1 := by simpa only [Complex.norm_of_nonneg hq0.le] using hq1
  have hmult : Multipliable (fun m : ℕ => 1-ModularForm.eta_q m ((r/2:ℂ)*Complex.I)) := by
    simpa only [eta_q_imaginary,Complex.ofReal_pow] using ModularForm.multipliable_one_sub_pow hqnorm
  rw [ModularForm.eta,norm_mul,Function.Periodic.norm_qParam,hmult.norm_tprod]
  congr 1
  · congr 1
    norm_num [Complex.mul_im,Complex.div_re,Complex.normSq]
    ring
  · apply tprod_congr
    intro m
    rw [eta_q_imaginary]
    have hp : 0 < 1-Real.exp (-Real.pi*r)^(m+1) :=
      sub_pos.mpr (pow_lt_one₀ hq0.le hq1 (Nat.succ_ne_zero m))
    rw [← Complex.ofReal_one,← Complex.ofReal_pow,← Complex.ofReal_sub,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hp]

/-- The Bose series at exponent one is the real logarithm of the imaginary-axis eta product. -/
theorem etaLog : Contracts.etaLog := by
  intro r hr
  let q := Real.exp (-Real.pi*r)
  have hq0 : 0 < q := Real.exp_pos _
  have hq1 : q < 1 := Real.exp_lt_one_iff.mpr (by nlinarith [Real.pi_pos])
  have hgeom : Summable (fun m : ℕ => q^(m+1)) :=
    (summable_nat_add_iff 1).mpr (summable_geometric_of_lt_one hq0.le hq1)
  have hlogs : Summable (fun m : ℕ => Real.log (1-q^(m+1))) := by
    simpa only [sub_eq_add_neg] using Real.summable_log_one_add_of_summable hgeom.neg
  have hpos (m : ℕ) : 0 < 1-q^(m+1) := sub_pos.mpr (pow_lt_one₀ hq0.le hq1 (Nat.succ_ne_zero m))
  have hprod := Real.rexp_tsum_eq_tprod hpos hlogs
  have hs : S 1 r = -(∑' m : ℕ, Real.log (1-q^(m+1))) :=
    (S_one_lambert r hr).trans (lambert_log q hq0 hq1)
  have hn := eta_norm_product r hr
  change ‖ModularForm.eta ((r/2:ℂ)*Complex.I)‖ = Real.exp (-Real.pi*r/24)*(∏' m : ℕ, (1-q^(m+1))) at hn
  rw [← hprod,← Real.exp_add] at hn
  have hl := congrArg Real.log hn
  rw [Real.log_exp] at hl
  linarith


end Plouffe.Proofs.EtaLog
