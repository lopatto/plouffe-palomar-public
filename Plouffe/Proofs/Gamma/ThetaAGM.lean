/-
Copyright (c) 2026 Patrick Lopatto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Lopatto
-/
module

public import Mathlib.NumberTheory.ModularForms.JacobiTheta.OneVariable
public import Mathlib.Analysis.SpecialFunctions.ArithmeticGeometricMean
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.NormNum

public section
namespace Plouffe.Proofs.Gamma.ThetaAGM

open Filter Topology

private theorem gaussian_term (r : ℝ) (n : ℤ) :
    Complex.exp ((Real.pi:ℂ)*Complex.I*(n:ℂ)^2*((r:ℂ)*Complex.I)) =
      ((Real.exp (-Real.pi*r*(n:ℝ)^2):ℝ):ℂ) := by
  rw [Complex.ofReal_exp]
  congr 1
  push_cast
  ring_nf
  norm_num

/-- Absolute summability on the imaginary axis, using the canonical theta summability theorem. -/
theorem gaussian_summable (r : ℝ) (hr : 0 < r) :
    Summable (fun n : ℤ => Real.exp (-Real.pi*r*(n:ℝ)^2)) := by
  have hτ : 0 < ((r:ℂ)*Complex.I).im := by simpa using hr
  have hC := (hasSum_jacobiTheta₂_term 0 hτ).summable
  simp only [jacobiTheta₂_term,mul_zero,zero_add] at hC
  have hC' : Summable (fun n : ℤ => ((Real.exp (-Real.pi*r*(n:ℝ)^2):ℝ):ℂ)) := by
    simpa only [gaussian_term] using hC
  have hR := (Complex.reCLM.hasSum hC'.hasSum).summable
  change Summable (fun n : ℤ => (((Real.exp (-Real.pi*r*(n:ℝ)^2):ℝ):ℂ)).re) at hR
  simpa only [Complex.ofReal_re] using hR

/-- The native Jacobi theta restricts to the positive real Gaussian sum. -/
theorem theta_axis (r : ℝ) (hr : 0 < r) :
    jacobiTheta ((r:ℂ)*Complex.I) = ((∑' n : ℤ, Real.exp (-Real.pi*r*(n:ℝ)^2):ℝ):ℂ) := by
  have hsum := gaussian_summable r hr
  unfold jacobiTheta
  rw [tsum_congr (gaussian_term r)]
  exact (Complex.ofReal_tsum _).symm

theorem theta_axis_im (r : ℝ) (hr : 0 < r) : (jacobiTheta ((r:ℂ)*Complex.I)).im = 0 := by
  rw [theta_axis r hr]
  rfl

theorem theta_axis_pos (r : ℝ) (hr : 0 < r) : 0 < (jacobiTheta ((r:ℂ)*Complex.I)).re := by
  rw [theta_axis r hr]
  simp only [Complex.ofReal_re]
  exact (gaussian_summable r hr).tsum_pos (fun _ => (Real.exp_pos _).le) 0 (Real.exp_pos _)

/-- Native theta tends to one along the dyadic imaginary-axis parameters used by AGM iteration. -/
theorem theta_dyadic_tendsto :
    Tendsto (fun n : ℕ => jacobiTheta ((((2:ℝ)^n:ℝ):ℂ)*Complex.I)) atTop (𝓝 (1:ℂ)) := by
  have htop : Tendsto (fun n : ℕ => (2:ℝ)^n) atTop atTop :=
    tendsto_pow_atTop_atTop_of_one_lt (by norm_num)
  have he : Tendsto (fun n : ℕ => Real.exp (-Real.pi*(2:ℝ)^n)) atTop (𝓝 (0:ℝ)) := by
    simpa only [Function.comp_def,neg_mul] using Real.tendsto_exp_neg_atTop_nhds_zero.comp (htop.const_mul_atTop Real.pi_pos)
  have hden : Tendsto (fun n : ℕ => 1-Real.exp (-Real.pi*(2:ℝ)^n)) atTop (𝓝 (1:ℝ)) := by
    simpa using tendsto_const_nhds.sub he
  have hbound : Tendsto (fun n : ℕ => 2/(1-Real.exp (-Real.pi*(2:ℝ)^n))*
      Real.exp (-Real.pi*(2:ℝ)^n)) atTop (𝓝 (0:ℝ)) := by
    simpa using (tendsto_const_nhds.div hden (by norm_num : (1:ℝ) ≠ 0)).mul he
  have hn : Tendsto (fun n : ℕ => ‖jacobiTheta ((((2:ℝ)^n:ℝ):ℂ)*Complex.I)-1‖) atTop (𝓝 (0:ℝ)) := by
    apply squeeze_zero (fun _ => norm_nonneg _) _ hbound
    intro n
    have him : (((((2:ℝ)^n:ℝ):ℂ)*Complex.I)).im = (2:ℝ)^n := by
      simp only [Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im,Complex.I_im,Complex.I_re,mul_one,mul_zero,add_zero]
    have hτ : 0 < (((((2:ℝ)^n:ℝ):ℂ)*Complex.I)).im := by rw [him]; positivity
    have hh := norm_jacobiTheta_sub_one_le hτ
    rw [him] at hh
    exact hh
  exact tendsto_iff_norm_sub_tendsto_zero.mpr hn

/-- The parity split of the Gaussian lattice, used for theta duplication. -/
@[expose] noncomputable def gaussianParityEquiv : ((ℤ × ℤ) ⊕ (ℤ × ℤ)) ≃ (ℤ × ℤ) :=
  Equiv.ofBijective (fun x => x.elim (fun p => (p.1+p.2,p.1-p.2))
    (fun p => (p.1+p.2+1,p.1-p.2))) (by
    constructor
    · rintro (⟨r,s⟩|⟨r,s⟩) (⟨u,v⟩|⟨u,v⟩) h
      all_goals
        have h1 := congrArg Prod.fst h
        have h2 := congrArg Prod.snd h
        dsimp at h1 h2
      · congr 1
        apply Prod.ext <;> omega
      · omega
      · omega
      · congr 1
        apply Prod.ext <;> omega
    · rintro ⟨m,n⟩
      by_cases h : (m+n)%2=0
      · refine ⟨Sum.inl ((m+n)/2,(m-n)/2),?_⟩
        apply Prod.ext <;> dsimp <;> omega
      · refine ⟨Sum.inr ((m+n-1)/2,(m-n-1)/2),?_⟩
        apply Prod.ext <;> dsimp <;> omega)

private theorem gaussian_pair_even (r : ℝ) (m n : ℤ) :
    Real.exp (-Real.pi*r*((m+n:ℤ):ℝ)^2)*Real.exp (-Real.pi*r*((m-n:ℤ):ℝ)^2) =
    Real.exp (-Real.pi*(2*r)*(m:ℝ)^2)*Real.exp (-Real.pi*(2*r)*(n:ℝ)^2) := by
  rw [← Real.exp_add,← Real.exp_add]
  congr 1
  push_cast
  ring

private theorem gaussian_pair_odd (r : ℝ) (m n : ℤ) :
    Real.exp (-Real.pi*r*((m+n+1:ℤ):ℝ)^2)*Real.exp (-Real.pi*r*((m-n:ℤ):ℝ)^2) =
    Real.exp (-Real.pi*(2*r)*((m:ℝ)+1/2)^2)*Real.exp (-Real.pi*(2*r)*((n:ℝ)+1/2)^2) := by
  rw [← Real.exp_add,← Real.exp_add]
  congr 1
  push_cast
  ring

/-- The shifted Gaussian needed in the odd lattice coset is absolutely summable. -/
theorem shifted_gaussian_summable (r : ℝ) (hr : 0 < r) :
    Summable (fun n : ℤ => Real.exp (-Real.pi*(2*r)*((n:ℝ)+1/2)^2)) := by
  have h := (gaussian_summable r hr).mul_left (Real.exp (Real.pi*r/2))
  apply h.of_nonneg_of_le (fun _ => (Real.exp_pos _).le)
  intro n
  rw [← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have hs := mul_nonneg (mul_pos Real.pi_pos hr).le (sq_nonneg ((n:ℝ)+1))
  nlinarith

/-- Native theta duplication obtained by an absolutely summable Gaussian-lattice reindexing. -/
theorem theta_duplication (r : ℝ) (hr : 0 < r) :
    (jacobiTheta ((r:ℂ)*Complex.I)).re^2 =
      (jacobiTheta (((2*r:ℝ):ℂ)*Complex.I)).re^2+
      (∑' n : ℤ, Real.exp (-Real.pi*(2*r)*((n:ℝ)+1/2)^2))^2 := by
  have h := gaussian_summable r hr
  have h2 := gaussian_summable (2*r) (by positivity)
  have hshift := shifted_gaussian_summable r hr
  have hp := h.mul_of_nonneg h (fun _ => (Real.exp_pos _).le) (fun _ => (Real.exp_pos _).le)
  have hp2 := h2.mul_of_nonneg h2 (fun _ => (Real.exp_pos _).le) (fun _ => (Real.exp_pos _).le)
  have hps := hshift.mul_of_nonneg hshift (fun _ => (Real.exp_pos _).le) (fun _ => (Real.exp_pos _).le)
  have hcomp := hp.comp_injective gaussianParityEquiv.injective
  rw [theta_axis r hr,theta_axis (2*r) (by positivity)]
  simp only [Complex.ofReal_re]
  conv_lhs => rw [pow_two]
  conv_rhs => lhs; rw [pow_two]
  conv_rhs => rhs; rw [pow_two]
  rw [h.tsum_mul_tsum h hp,h2.tsum_mul_tsum h2 hp2,hshift.tsum_mul_tsum hshift hps]
  rw [← gaussianParityEquiv.tsum_eq (fun p : ℤ × ℤ =>
    Real.exp (-Real.pi*r*(p.1:ℝ)^2)*Real.exp (-Real.pi*r*(p.2:ℝ)^2))]
  have hs := Summable.tsum_sum (hcomp.comp_injective Sum.inl_injective) (hcomp.comp_injective Sum.inr_injective)
  simp only [Function.comp_def] at hs
  rw [hs]
  congr 1
  · apply tsum_congr
    rintro ⟨m,n⟩
    exact gaussian_pair_even r m n
  · apply tsum_congr
    rintro ⟨m,n⟩
    exact gaussian_pair_odd r m n

#print axioms gaussian_summable
#print axioms theta_axis
#print axioms theta_axis_pos
#print axioms theta_dyadic_tendsto
#print axioms theta_duplication

end Plouffe.Proofs.Gamma.ThetaAGM
