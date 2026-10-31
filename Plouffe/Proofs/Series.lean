/-
Copyright (c) 2026 Patrick Lopatto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Lopatto
-/
module

public import Plouffe.Infrastructure.Series
public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.Topology.Algebra.InfiniteSum.Order
public import Mathlib.Topology.Algebra.InfiniteSum.Group

public section
namespace Plouffe.Proofs.Series

private theorem boseTerm_bound (s j : ℕ) {a : ℝ} (ha : 0 < a) :
    |1 / (((j+1:ℕ):ℝ)^s * (Real.exp (a*((j+1:ℕ):ℝ))-1))| ≤
      (1/(Real.exp a-1))*Real.exp (-a)^j := by
  have hj : (1:ℝ) ≤ ((j+1:ℕ):ℝ) := by exact_mod_cast (Nat.succ_le_succ (Nat.zero_le j))
  have hw : (1:ℝ) ≤ ((j+1:ℕ):ℝ)^s := one_le_pow₀ hj
  have hx : 1 < Real.exp a := Real.one_lt_exp_iff.mpr ha
  have hy : 1 ≤ Real.exp (a*(j:ℝ)) := Real.one_le_exp_iff.mpr (mul_nonneg ha.le (Nat.cast_nonneg j))
  have heq : Real.exp (a*((j+1:ℕ):ℝ)) = Real.exp (a*(j:ℝ))*Real.exp a := by
    rw [Nat.cast_add, Nat.cast_one, mul_add, mul_one, Real.exp_add]
  have hd : 0 < Real.exp (a*((j+1:ℕ):ℝ))-1 := by rw [heq]; nlinarith
  have hsmall : 0 < (Real.exp a-1)*Real.exp (a*(j:ℝ)) := mul_pos (sub_pos.mpr hx) (Real.exp_pos _)
  rw [abs_of_pos (one_div_pos.mpr (mul_pos (by positivity) hd))]
  calc
    _ ≤ 1/(Real.exp (a*((j+1:ℕ):ℝ))-1) :=
      one_div_le_one_div_of_le hd (by nlinarith)
    _ ≤ 1/((Real.exp a-1)*Real.exp (a*(j:ℝ))) :=
      one_div_le_one_div_of_le hsmall (by rw [heq]; nlinarith)
    _ = _ := by
      rw [← Real.exp_nat_mul]
      simp only [mul_neg, Real.exp_neg, one_div, mul_inv_rev]
      simp [mul_comm]

/-- Fixed positive parameter geometric bound for the Bose series. -/
theorem geometricMajorant : Contracts.geometricMajorant := by
  intro s r hr
  have ha : 0 < Real.pi*r := mul_pos Real.pi_pos hr
  refine ⟨1/(Real.exp (Real.pi*r)-1), one_div_pos.mpr (sub_pos.mpr (Real.one_lt_exp_iff.mpr ha)), ?_⟩
  intro j
  simpa only [neg_mul] using boseTerm_bound s j ha

/-- Absolute convergence of every natural-power Bose series at a positive parameter. -/
theorem summableS : Contracts.summableS := by
  intro s r hr
  obtain ⟨C,hC,hbound⟩ := geometricMajorant s r hr
  have hq : Real.exp (-Real.pi*r) < 1 := Real.exp_lt_one_iff.mpr (by nlinarith [Real.pi_pos])
  have hg := (summable_geometric_of_lt_one (Real.exp_nonneg (-Real.pi*r)) hq).mul_left C
  apply Summable.of_norm
  exact hg.of_nonneg_of_le (fun _ => norm_nonneg _) (fun j => by simpa only [Real.norm_eq_abs] using hbound j)

private theorem boseDen_pos (s j : ℕ) {r : ℝ} (hr : 0 < r) :
    0 < ((j+1:ℕ):ℝ)^s * (Real.exp (Real.pi*r*((j+1:ℕ):ℝ))-1) := by
  have hk : (0:ℝ) < ((j+1:ℕ):ℝ) := by positivity
  exact mul_pos (pow_pos hk s)
    (sub_pos.mpr (Real.one_lt_exp_iff.mpr (mul_pos (mul_pos Real.pi_pos hr) hk)))

private theorem fermiDen_pos (s j : ℕ) (r : ℝ) :
    0 < ((j+1:ℕ):ℝ)^s * (Real.exp (Real.pi*r*((j+1:ℕ):ℝ))+1) := by
  exact mul_pos (pow_pos (by positivity) s) (by positivity)

/-- The Fermi terms are dominated by their summable Bose counterparts. -/
theorem summableT : Contracts.summableT := by
  intro s r hr
  apply (summableS s r hr).of_nonneg_of_le
  · intro j
    exact (one_div_pos.mpr (fermiDen_pos s j r)).le
  · intro j
    exact one_div_le_one_div_of_le (boseDen_pos s j hr) (by nlinarith [pow_pos (show (0:ℝ)<((j+1:ℕ):ℝ) by positivity) s])

/-- Every positive-parameter Bose and Fermi series is strictly positive. -/
theorem positive : Contracts.positive := by
  intro s r hr
  constructor
  · exact (summableS s r hr).tsum_pos (fun j => (one_div_pos.mpr (boseDen_pos s j hr)).le) 0
      (one_div_pos.mpr (boseDen_pos s 0 hr))
  · exact (summableT s r hr).tsum_pos (fun j => (one_div_pos.mpr (fermiDen_pos s j r)).le) 0
      (one_div_pos.mpr (fermiDen_pos s 0 r))

/-- Strict parameter monotonicity follows from strict termwise exponential monotonicity. -/
theorem strictParameter : Contracts.strictParameter := by
  intro s r t hr hrt
  have hterm : ∀ j : ℕ,
      1 / (((j+1:ℕ):ℝ)^s*(Real.exp (Real.pi*t*((j+1:ℕ):ℝ))-1)) <
      1 / (((j+1:ℕ):ℝ)^s*(Real.exp (Real.pi*r*((j+1:ℕ):ℝ))-1)) := by
    intro j
    apply one_div_lt_one_div_of_lt (boseDen_pos s j hr)
    apply mul_lt_mul_of_pos_left _ (pow_pos (by positivity) s)
    apply sub_lt_sub_right
    apply Real.exp_lt_exp.mpr
    exact mul_lt_mul_of_pos_right (mul_lt_mul_of_pos_left hrt Real.pi_pos) (by positivity)
  exact Summable.tsum_lt_tsum (fun j => (hterm j).le) (hterm 0)
    (summableS s t (hr.trans hrt)) (summableS s r hr)

/-- Pointwise Fermi/Bose identity summed only after both Bose series converge. -/
theorem fermiBose : Contracts.fermiBose := by
  intro s r hr
  have h2r : 0 < 2*r := by positivity
  have hS := summableS s r hr
  have hS2 := summableS s (2*r) h2r
  have hpoint : ∀ j : ℕ,
      1 / (((j+1:ℕ):ℝ)^s*(Real.exp (Real.pi*r*((j+1:ℕ):ℝ))+1)) =
      1 / (((j+1:ℕ):ℝ)^s*(Real.exp (Real.pi*r*((j+1:ℕ):ℝ))-1)) -
      2*(1 / (((j+1:ℕ):ℝ)^s*(Real.exp (Real.pi*(2*r)*((j+1:ℕ):ℝ))-1))) := by
    intro j
    have hx : 1 < Real.exp (Real.pi*r*((j+1:ℕ):ℝ)) :=
      Real.one_lt_exp_iff.mpr (mul_pos (mul_pos Real.pi_pos hr) (by positivity))
    have hw : ((j+1:ℕ):ℝ)^s ≠ 0 := ne_of_gt (pow_pos (by positivity) s)
    have hm : Real.exp (Real.pi*r*((j+1:ℕ):ℝ))-1 ≠ 0 := ne_of_gt (sub_pos.mpr hx)
    have hp : Real.exp (Real.pi*r*((j+1:ℕ):ℝ))+1 ≠ 0 := by positivity
    have hs : Real.exp (Real.pi*r*((j+1:ℕ):ℝ))^2-1 ≠ 0 := by nlinarith
    have he : Real.exp (Real.pi*(2*r)*((j+1:ℕ):ℝ)) =
        Real.exp (Real.pi*r*((j+1:ℕ):ℝ))^2 := by
      rw [show Real.pi*(2*r)*((j+1:ℕ):ℝ) = Real.pi*r*((j+1:ℕ):ℝ)+Real.pi*r*((j+1:ℕ):ℝ) by ring,
        Real.exp_add, pow_two]
    rw [he]
    field_simp
    ring
  unfold S T
  rw [tsum_congr hpoint, hS.tsum_sub (hS2.mul_left 2), hS2.tsum_mul_left]

/-- Restriction of the complex Lambert series to positive real arguments. -/
theorem lambertReal : Contracts.lambertReal := by
  intro n a ha
  have hr : 0 < 2*a/Real.pi := div_pos (by positivity) Real.pi_pos
  have hsum := summableS (2*n+1) (2*a/Real.pi) hr
  have hsumC := Complex.ofRealCLM.hasSum hsum.hasSum
  unfold L S
  rw [Complex.ofReal_tsum]
  apply tsum_congr
  intro j
  push_cast
  congr 3
  apply congrArg Complex.exp
  have hpi : (Real.pi:ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  field_simp

/-- Absolute convergence in the right half-plane by comparison with the real Bose series. -/
theorem summableL : Contracts.summableL := by
  intro n a ha
  have hr : 0 < 2*a.re/Real.pi := div_pos (by positivity) Real.pi_pos
  have hreal := summableS (2*n+1) (2*a.re/Real.pi) hr
  apply Summable.of_norm
  apply hreal.of_nonneg_of_le (fun _ => norm_nonneg _)
  intro j
  have harg : Real.pi*(2*a.re/Real.pi)*((j+1:ℕ):ℝ) = 2*a.re*((j+1:ℕ):ℝ) := by field_simp
  have hden : 0 < Real.exp (2*a.re*((j+1:ℕ):ℝ))-1 :=
    sub_pos.mpr (Real.one_lt_exp_iff.mpr (mul_pos (mul_pos (by norm_num) ha) (by positivity)))
  have hb := norm_sub_norm_le (Complex.exp (2*a*((j+1:ℕ):ℂ))) (1:ℂ)
  have hb' : Real.exp (2*a.re*((j+1:ℕ):ℝ))-1 ≤ ‖Complex.exp (2*a*((j+1:ℕ):ℂ))-1‖ := by
    simpa [Complex.norm_exp, Complex.mul_re] using hb
  rw [harg, norm_div, norm_one, norm_mul, norm_pow, Complex.norm_natCast]
  exact one_div_le_one_div_of_le (mul_pos (pow_pos (by positivity) _) hden)
    (mul_le_mul_of_nonneg_left hb' (by positivity))


end Plouffe.Proofs.Series
