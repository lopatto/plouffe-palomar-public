/-
Copyright (c) 2026 Patrick Lopatto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Lopatto
-/
module

public import Plouffe.Proofs.Gamma.ThetaAGM

@[expose] public section
namespace Plouffe.Proofs.Gamma.ThetaAGM

/-- The real Gaussian expression `exp(-π*r*n²)` on integer indices. -/
noncomputable def gaussian (r : ℝ) (n : ℤ) : ℝ := Real.exp (-Real.pi*r*(n:ℝ)^2)
/-- The real half-shifted Gaussian expression `exp(-π*r*(n+1/2)²)` on integer indices. -/
noncomputable def shiftGaussian (r : ℝ) (n : ℤ) : ℝ := Real.exp (-Real.pi*r*((n:ℝ)+1/2)^2)
/-- The real integer power `(-1)^n`. -/
noncomputable def alternatingSign (n : ℤ) : ℝ := (-1:ℝ)^n

/-- The real alternating Gaussian companion to the native theta function. -/
noncomputable def alternate (r : ℝ) : ℝ := ∑' n : ℤ, alternatingSign n*gaussian r n

private theorem chi_norm (n : ℤ) : ‖alternatingSign n‖ = 1 := by simp [alternatingSign]
private theorem chi_add (m n : ℤ) : alternatingSign (m+n) = alternatingSign m*alternatingSign n := by
  exact zpow_add₀ (by norm_num) _ _
private theorem chi_sub (m n : ℤ) : alternatingSign (m-n) = alternatingSign m*alternatingSign n := by
  rw [alternatingSign, zpow_sub₀ (by norm_num), div_eq_mul_inv]
  simp only [← inv_zpow,inv_neg,inv_one]
  rfl
private theorem chi_two (n : ℤ) : alternatingSign (2*n) = 1 := by
  exact (even_two_mul n).neg_one_zpow

private theorem signed_summable {f : ℤ → ℝ} (hf : Summable f) (hp : ∀ n, 0 ≤ f n) :
    Summable (fun n => alternatingSign n*f n) := by
  apply hf.of_norm_bounded
  intro n
  simp only [norm_mul,chi_norm,Real.norm_of_nonneg (hp n),one_mul,le_refl]

private theorem signed_pair_summable {f h : ℤ → ℝ} (hf : Summable f) (hh : Summable h)
    (hfp : ∀ n, 0 ≤ f n) (hhp : ∀ n, 0 ≤ h n) :
    Summable (fun p : ℤ × ℤ => alternatingSign p.1*f p.1*(alternatingSign p.2*h p.2)) := by
  apply (hf.mul_of_nonneg hh hfp hhp).of_norm_bounded
  intro p
  simp only [norm_mul,chi_norm,Real.norm_of_nonneg (hfp p.1),Real.norm_of_nonneg (hhp p.2),one_mul,le_refl]

private theorem even_energy (r : ℝ) (m n : ℤ) : gaussian r (m+n)*gaussian r (m-n) = gaussian (2*r) m*gaussian (2*r) n := by
  simp only [gaussian,← Real.exp_add]
  congr 1
  push_cast
  ring
private theorem odd_energy (r : ℝ) (m n : ℤ) : gaussian r (m+n+1)*gaussian r (m-n) = shiftGaussian (2*r) m*shiftGaussian (2*r) n := by
  simp only [gaussian,shiftGaussian,← Real.exp_add]
  congr 1
  push_cast
  ring

/-- The alternating half-shifted Gaussian cancels under reflection about -1/2. -/
theorem alternate_shift_zero (r : ℝ) (hr : 0 < r) :
    (∑' n : ℤ, alternatingSign n*shiftGaussian r n) = 0 := by
  have hshift : Summable (shiftGaussian r) := by
    change Summable (fun n : ℤ => Real.exp (-Real.pi*r*((n:ℝ)+1/2)^2))
    simpa only [show 2*(r/2)=r by ring] using shifted_gaussian_summable (r/2) (by positivity)
  have hs := signed_summable hshift (fun n => (Real.exp_pos _).le)
  let e : ℤ ≃ ℤ := ⟨(fun n => -n-1),(fun n => -n-1),(by intro n; dsimp; omega),(by intro n; dsimp; omega)⟩
  have he := e.tsum_eq (fun n => alternatingSign n*shiftGaussian r n)
  have hterm (n : ℤ) : alternatingSign (-n-1)*shiftGaussian r (-n-1) = -(alternatingSign n*shiftGaussian r n) := by
    have hc : alternatingSign (-n-1) = -alternatingSign n := by
      rw [alternatingSign, zpow_sub₀ (by norm_num), zpow_neg, zpow_one]
      simp only [← inv_zpow,inv_neg,inv_one]
      change (-1:ℝ)^n / (-1) = -((-1:ℝ)^n)
      ring
    have hg : shiftGaussian r (-n-1) = shiftGaussian r n := by
      simp only [shiftGaussian]
      congr 1
      push_cast
      ring
    rw [hc,hg]
    ring
  have hneg : (∑' n : ℤ, alternatingSign n*shiftGaussian r n) = -(∑' n : ℤ, alternatingSign n*shiftGaussian r n) := by
    calc
      _ = ∑' n : ℤ, alternatingSign (-n-1)*shiftGaussian r (-n-1) := he.symm
      _ = ∑' n : ℤ, -(alternatingSign n*shiftGaussian r n) := tsum_congr hterm
      _ = _ := tsum_neg
  linarith

private theorem parity_tsum (f : ℤ × ℤ → ℝ) (hf : Summable f) :
    (∑' p, f p) = (∑' p : ℤ × ℤ, f (p.1+p.2,p.1-p.2))+
      ∑' p : ℤ × ℤ, f (p.1+p.2+1,p.1-p.2) := by
  have hc := hf.comp_injective gaussianParityEquiv.injective
  rw [← gaussianParityEquiv.tsum_eq f]
  have hs := Summable.tsum_sum (hc.comp_injective Sum.inl_injective) (hc.comp_injective Sum.inr_injective)
  simp only [Function.comp_def] at hs
  exact hs

private theorem signed_even (m n : ℤ) : alternatingSign (m+n)*alternatingSign (m-n) = 1 := by
  rw [← chi_add,show (m+n)+(m-n)=2*m by ring,chi_two]
private theorem signed_odd (m n : ℤ) : alternatingSign (m+n+1)*alternatingSign (m-n) = -1 := by
  rw [← chi_add,show (m+n+1)+(m-n)=2*m+1 by ring,chi_add,chi_two]
  norm_num [alternatingSign]

/-- The alternating square is the difference of the two Gaussian parity-coset squares. -/
theorem alternate_duplication (r : ℝ) (hr : 0 < r) :
    (alternate r)^2 = (jacobiTheta (((2*r:ℝ):ℂ)*Complex.I)).re^2-
      (∑' n : ℤ, shiftGaussian (2*r) n)^2 := by
  have h : Summable (gaussian r) := gaussian_summable r hr
  have h2 : Summable (gaussian (2*r)) := gaussian_summable (2*r) (by positivity)
  have hshift : Summable (shiftGaussian (2*r)) := shifted_gaussian_summable r hr
  have hpos (n : ℤ) : 0 ≤ gaussian r n := (Real.exp_pos _).le
  have h2pos (n : ℤ) : 0 ≤ gaussian (2*r) n := (Real.exp_pos _).le
  have hspos (n : ℤ) : 0 ≤ shiftGaussian (2*r) n := (Real.exp_pos _).le
  have ha := signed_summable h hpos
  have hp := signed_pair_summable h h hpos hpos
  rw [theta_axis (2*r) (by positivity)]
  simp only [Complex.ofReal_re]
  change (∑' n : ℤ, alternatingSign n*gaussian r n)^2 =
    (∑' n : ℤ, gaussian (2*r) n)^2-(∑' n : ℤ, shiftGaussian (2*r) n)^2
  conv_lhs => rw [pow_two]
  conv_rhs => lhs; rw [pow_two]
  conv_rhs => rhs; rw [pow_two]
  rw [ha.tsum_mul_tsum ha hp,h2.tsum_mul_tsum h2 (h2.mul_of_nonneg h2 h2pos h2pos),
    hshift.tsum_mul_tsum hshift (hshift.mul_of_nonneg hshift hspos hspos),parity_tsum _ hp]
  have he (p : ℤ × ℤ) :
      alternatingSign (p.1+p.2)*gaussian r (p.1+p.2)*(alternatingSign (p.1-p.2)*gaussian r (p.1-p.2)) =
      gaussian (2*r) p.1*gaussian (2*r) p.2 := by
    calc
      _ = (alternatingSign (p.1+p.2)*alternatingSign (p.1-p.2))*(gaussian r (p.1+p.2)*gaussian r (p.1-p.2)) := by ring
      _ = _ := by rw [signed_even,one_mul,even_energy]
  have ho (p : ℤ × ℤ) :
      alternatingSign (p.1+p.2+1)*gaussian r (p.1+p.2+1)*(alternatingSign (p.1-p.2)*gaussian r (p.1-p.2)) =
      -(shiftGaussian (2*r) p.1*shiftGaussian (2*r) p.2) := by
    calc
      _ = (alternatingSign (p.1+p.2+1)*alternatingSign (p.1-p.2))*(gaussian r (p.1+p.2+1)*gaussian r (p.1-p.2)) := by ring
      _ = _ := by rw [signed_odd,neg_one_mul,odd_energy]
  rw [tsum_congr he,tsum_congr ho,tsum_neg]
  rfl

/-- Arithmetic-mean step for the two squared theta companions. -/
theorem alternate_arithmetic (r : ℝ) (hr : 0 < r) :
    ((jacobiTheta ((r:ℂ)*Complex.I)).re^2+(alternate r)^2)/2 =
      (jacobiTheta (((2*r:ℝ):ℂ)*Complex.I)).re^2 := by
  have h := theta_duplication r hr
  have ha := alternate_duplication r hr
  change (alternate r)^2 = (jacobiTheta (((2*r:ℝ):ℂ)*Complex.I)).re^2-
    (∑' n : ℤ, Real.exp (-Real.pi*(2*r)*((n:ℝ)+1/2)^2))^2 at ha
  linarith

/-- Geometric-mean step for the squared theta companions. -/
theorem alternate_geometric (r : ℝ) (hr : 0 < r) :
    (jacobiTheta ((r:ℂ)*Complex.I)).re*alternate r = (alternate (2*r))^2 := by
  have h : Summable (gaussian r) := gaussian_summable r hr
  have h2 : Summable (gaussian (2*r)) := gaussian_summable (2*r) (by positivity)
  have hshift : Summable (shiftGaussian (2*r)) := shifted_gaussian_summable r hr
  have hpos (n : ℤ) : 0 ≤ gaussian r n := (Real.exp_pos _).le
  have h2pos (n : ℤ) : 0 ≤ gaussian (2*r) n := (Real.exp_pos _).le
  have hspos (n : ℤ) : 0 ≤ shiftGaussian (2*r) n := (Real.exp_pos _).le
  have ha := signed_summable h hpos
  have ha2 := signed_summable h2 h2pos
  have hs := signed_summable hshift hspos
  have hp : Summable (fun p : ℤ × ℤ => gaussian r p.1*(alternatingSign p.2*gaussian r p.2)) := by
    apply (h.mul_of_nonneg h hpos hpos).of_norm_bounded
    intro p
    simp only [norm_mul,chi_norm,Real.norm_of_nonneg (hpos p.1),Real.norm_of_nonneg (hpos p.2),one_mul,le_refl]
  have he (p : ℤ × ℤ) : gaussian r (p.1+p.2)*(alternatingSign (p.1-p.2)*gaussian r (p.1-p.2)) =
      alternatingSign p.1*gaussian (2*r) p.1*(alternatingSign p.2*gaussian (2*r) p.2) := by
    rw [chi_sub]
    calc
      _ = (alternatingSign p.1*alternatingSign p.2)*(gaussian r (p.1+p.2)*gaussian r (p.1-p.2)) := by ring
      _ = _ := by rw [even_energy]; ring
  have ho (p : ℤ × ℤ) : gaussian r (p.1+p.2+1)*(alternatingSign (p.1-p.2)*gaussian r (p.1-p.2)) =
      alternatingSign p.1*shiftGaussian (2*r) p.1*(alternatingSign p.2*shiftGaussian (2*r) p.2) := by
    rw [chi_sub]
    calc
      _ = (alternatingSign p.1*alternatingSign p.2)*(gaussian r (p.1+p.2+1)*gaussian r (p.1-p.2)) := by ring
      _ = _ := by rw [odd_energy]; ring
  rw [theta_axis r hr]
  simp only [Complex.ofReal_re]
  change (∑' n : ℤ, gaussian r n)*(∑' n : ℤ, alternatingSign n*gaussian r n) =
    (∑' n : ℤ, alternatingSign n*gaussian (2*r) n)^2
  rw [h.tsum_mul_tsum ha hp,parity_tsum _ hp,tsum_congr he,tsum_congr ho,
    ← ha2.tsum_mul_tsum ha2 (signed_pair_summable h2 h2 h2pos h2pos),
    ← hs.tsum_mul_tsum hs (signed_pair_summable hshift hshift hspos hspos),
    alternate_shift_zero (2*r) (by positivity),mul_zero,add_zero,pow_two]

#print axioms alternate_shift_zero
#print axioms alternate_duplication
#print axioms alternate_arithmetic
#print axioms alternate_geometric

end Plouffe.Proofs.Gamma.ThetaAGM
