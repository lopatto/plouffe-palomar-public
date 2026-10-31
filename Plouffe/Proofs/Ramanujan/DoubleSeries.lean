/-
Copyright (c) 2026 Patrick Lopatto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Lopatto
-/
module

public import Plouffe.Proofs.Series
public import Plouffe.Proofs.Double
public import Plouffe.Proofs.Coth
public import Plouffe.Proofs.Elementary
public import Plouffe.Proofs.Zeta
public import Mathlib.NumberTheory.LSeries.HurwitzZetaValues
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.LinearCombination

public section
namespace Plouffe.Proofs.Ramanujan

private theorem exp_sub_one_ne_zero {z : ℂ} (hz : 0 < z.re) : Complex.exp z-1 ≠ 0 := by
  apply sub_ne_zero.mpr
  intro h
  have hn := congrArg norm h
  rw [Complex.norm_exp, norm_one] at hn
  exact (ne_of_gt (Real.one_lt_exp_iff.mpr hz)) hn

private theorem kernel_ne_zero (a b : ℂ) (ha : 0 < a.re) (hb : 0 < b.re) (k l : ℕ) :
    a*((k+1:ℕ):ℂ)^2+b*((l+1:ℕ):ℂ)^2 ≠ 0 := by
  intro h
  have hRe : (a*((k+1:ℕ):ℂ)^2+b*((l+1:ℕ):ℂ)^2).re =
      a.re*((k+1:ℕ):ℝ)^2+b.re*((l+1:ℕ):ℝ)^2 := by
    simp [Complex.mul_re, pow_two]
  have hre : 0 < (a*((k+1:ℕ):ℂ)^2+b*((l+1:ℕ):ℂ)^2).re := by
    rw [hRe]
    exact add_pos (mul_pos ha (pow_pos (by positivity) _))
      (mul_pos hb (pow_pos (by positivity) _))
  rw [h] at hre
  exact (lt_irrefl 0) hre

private theorem weighted_coth_algebra (a k P E U : ℂ) (ha : a ≠ 0) (hk : k ≠ 0)
    (hp : P ≠ 0) (he : E-1 ≠ 0) (hc : (E+1)/(E-1)-1/(a*k) = 2*P*U) :
    (1/P)/2+1/(P*(E-1)) = (1/(P*k))/(2*a)+U := by
  field_simp at hc ⊢
  linear_combination hc

/-- Summing the weighted coth expansion with established absolute convergence. -/
theorem lambert_double_sum (n : ℕ) (a b : ℂ) (hn : 1 ≤ n)
    (ha : 0 < a.re) (hb : 0 < b.re) (hab : a*b = (Real.pi:ℂ)^2) :
    riemannZeta ((2*n+1:ℕ):ℂ)/2+L n a =
      riemannZeta ((2*n+2:ℕ):ℂ)/(2*a)+
      ∑' kl : ℕ × ℕ, 1 / (((kl.1+1:ℕ):ℂ)^(2*n) *
        (a*((kl.1+1:ℕ):ℂ)^2+b*((kl.2+1:ℕ):ℂ)^2)) := by
  have ha0 : a ≠ 0 := by intro h; simp [h] at ha
  have hD := Double.doubleSummable n a b hn ha hb
  have hZ := Zeta.zetaPositiveSeries (2*n+1) (by omega)
  have hE := Zeta.zetaPositiveSeries (2*n+2) (by omega)
  have hL := Series.summableL n a ha
  have hpoint (k : ℕ) :
      (1/((k+1:ℕ):ℂ)^(2*n+1))/2+
        1/(((k+1:ℕ):ℂ)^(2*n+1)*(Complex.exp (2*a*((k+1:ℕ):ℂ))-1)) =
      (1/((k+1:ℕ):ℂ)^(2*n+2))/(2*a)+
        ∑' l : ℕ, 1 / (((k+1:ℕ):ℂ)^(2*n) *
          (a*((k+1:ℕ):ℂ)^2+b*((l+1:ℕ):ℂ)^2)) := by
    have hk0 : ((k+1:ℕ):ℂ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero k
    have hak : 0 < (a*((k+1:ℕ):ℂ)).re := by
      simpa [Complex.mul_re] using mul_pos ha (show (0:ℝ) < ((k+1:ℕ):ℝ) by positivity)
    have he := exp_sub_one_ne_zero (show 0 < (2*a*((k+1:ℕ):ℂ)).re by
      simpa [Complex.mul_re] using mul_pos (mul_pos (show (0:ℝ)<2 by norm_num) ha)
        (show (0:ℝ) < ((k+1:ℕ):ℝ) by positivity))
    have hterm (l : ℕ) :
        2*(a*((k+1:ℕ):ℂ))/((a*((k+1:ℕ):ℂ))^2+(Real.pi:ℂ)^2*((l+1:ℕ):ℂ)^2) =
        2*((k+1:ℕ):ℂ)^(2*n+1)*
          (1 / (((k+1:ℕ):ℂ)^(2*n) *
            (a*((k+1:ℕ):ℂ)^2+b*((l+1:ℕ):ℂ)^2))) := by
      have hd := kernel_ne_zero a b ha hb k l
      have hfac : (a*((k+1:ℕ):ℂ))^2+(Real.pi:ℂ)^2*((l+1:ℕ):ℂ)^2 =
          a*(a*((k+1:ℕ):ℂ)^2+b*((l+1:ℕ):ℂ)^2) := by rw [← hab]; ring
      rw [hfac, pow_succ]
      field_simp
      ring
    have hc := Coth.cothKernel (a*((k+1:ℕ):ℂ)) hak
    change (Complex.exp (2*(a*((k+1:ℕ):ℂ)))+1)/(Complex.exp (2*(a*((k+1:ℕ):ℂ)))-1)-
      1/(a*((k+1:ℕ):ℂ)) = _ at hc
    rw [tsum_congr hterm, (hD.prod_factor k).tsum_mul_left] at hc
    have hearg : 2*(a*((k+1:ℕ):ℂ)) = 2*a*((k+1:ℕ):ℂ) := by ring
    rw [hearg] at hc
    rw [show 2*n+2 = (2*n+1)+1 by omega, pow_succ]
    exact weighted_coth_algebra a ((k+1:ℕ):ℂ) (((k+1:ℕ):ℂ)^(2*n+1))
      (Complex.exp (2*a*((k+1:ℕ):ℂ))) _ ha0 hk0 (pow_ne_zero _ hk0) he hc
  rw [hZ.2, show L n a = ∑' k : ℕ, 1/(((k+1:ℕ):ℂ)^(2*n+1)*
    (Complex.exp (2*a*((k+1:ℕ):ℂ))-1)) from rfl]
  rw [← tsum_div_const, ← (hZ.1.div_const 2).tsum_add hL,
    tsum_congr hpoint, (hE.1.div_const (2*a)).tsum_add hD.prod,
    tsum_div_const, ← hD.tsum_prod, ← hE.2]

end Plouffe.Proofs.Ramanujan
