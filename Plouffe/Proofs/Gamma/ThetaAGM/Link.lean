/-
Copyright (c) 2026 Patrick Lopatto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Lopatto
-/
module

public import Plouffe.Proofs.Gamma.ThetaAGM.Alternating

@[expose] public section
namespace Plouffe.Proofs.Gamma.ThetaAGM

open Filter Topology

/-- The square of the real part of `jacobiTheta (r*I)`, packaged as a nonnegative real. -/
noncomputable def thetaSquare (r : ℝ) : NNReal := ⟨(jacobiTheta ((r:ℂ)*Complex.I)).re^2,sq_nonneg _⟩
/-- The square of the alternating Gaussian `tsum`, packaged as a nonnegative real. -/
noncomputable def alternateSquare (r : ℝ) : NNReal := ⟨(alternate r)^2,sq_nonneg _⟩

theorem theta_mean_step (r : ℝ) (hr : 0 < r) :
    (NNReal.sqrt (thetaSquare r*alternateSquare r),(thetaSquare r+alternateSquare r)/2) =
      (alternateSquare (2*r),thetaSquare (2*r)) := by
  apply Prod.ext
  · apply NNReal.eq
    simp only [Real.coe_sqrt,NNReal.coe_mul]
    change Real.sqrt ((jacobiTheta ((r:ℂ)*Complex.I)).re^2*(alternate r)^2) = (alternate (2*r))^2
    rw [show (jacobiTheta ((r:ℂ)*Complex.I)).re^2*(alternate r)^2 = ((alternate (2*r))^2)^2 by
      rw [← mul_pow,alternate_geometric r hr]]
    exact Real.sqrt_sq (sq_nonneg _)
  · apply NNReal.eq
    exact alternate_arithmetic r hr

theorem theta_agm_sequences (n : ℕ) :
    NNReal.agmSequences (thetaSquare 1) (alternateSquare 1) n =
      (alternateSquare ((2:ℝ)^(n+1)),thetaSquare ((2:ℝ)^(n+1))) := by
  induction n with
  | zero => simpa only [NNReal.agmSequences_zero,Nat.zero_add,pow_one,mul_one] using theta_mean_step 1 (by norm_num)
  | succ n ih =>
    rw [NNReal.agmSequences_succ',ih]
    rw [show (2:ℝ)^(n+1+1)=2*(2:ℝ)^(n+1) by rw [pow_succ]; ring]
    rw [mul_comm (alternateSquare _) (thetaSquare _),add_comm (alternateSquare _) (thetaSquare _)]
    exact theta_mean_step ((2:ℝ)^(n+1)) (by positivity)

theorem theta_agm_one : NNReal.agm (thetaSquare 1) (alternateSquare 1) = 1 := by
  have ht := (Complex.continuous_re.tendsto (1:ℂ)).comp theta_dyadic_tendsto
  have ht2 : Tendsto (fun n : ℕ => (thetaSquare ((2:ℝ)^n):ℝ)) atTop (𝓝 (1:ℝ)) := by
    change Tendsto (fun n : ℕ => (jacobiTheta ((((2:ℝ)^n:ℝ):ℂ)*Complex.I)).re^2) atTop (𝓝 (1:ℝ))
    simpa only [Function.comp_def,Complex.one_re,one_pow] using ht.pow 2
  have hs : Tendsto (fun n : ℕ => ((NNReal.agmSequences (thetaSquare 1) (alternateSquare 1) n).2:ℝ))
      atTop (𝓝 (1:ℝ)) := by
    simp only [theta_agm_sequences]
    exact (tendsto_add_atTop_iff_nat 1).mpr ht2
  have ha := (NNReal.continuous_coe.tendsto (NNReal.agm (thetaSquare 1) (alternateSquare 1))).comp
    NNReal.tendsto_agmSequences_snd_agm
  apply NNReal.eq
  exact tendsto_nhds_unique ha hs

/-- The native modular theta transformation at twice the self-dual parameter. -/
theorem theta_half : jacobiTheta ((((1/2:ℝ):ℂ))*Complex.I) =
    ((Real.sqrt 2:ℝ):ℂ)*jacobiTheta ((2:ℂ)*Complex.I) := by
  let τ : UpperHalfPlane := ⟨(2:ℂ)*Complex.I,by norm_num⟩
  have hm := jacobiTheta_S_smul τ
  have harg : (((ModularGroup.S • τ):UpperHalfPlane):ℂ) = (((1/2:ℝ):ℂ))*Complex.I := by
    rw [UpperHalfPlane.modular_S_smul]
    change (-((2:ℂ)*Complex.I))⁻¹ = (((1/2:ℝ):ℂ))*Complex.I
    apply Complex.ext <;> norm_num
  rw [harg] at hm
  have hp : (-Complex.I*(τ:ℂ))^(1/2:ℂ) = ((Real.sqrt 2:ℝ):ℂ) := by
    have hbase : -Complex.I*(τ:ℂ) = (2:ℂ) := by dsimp [τ]; ring_nf; norm_num
    rw [hbase]
    have hc := Complex.ofReal_cpow (by norm_num : (0:ℝ) ≤ 2) (1/2:ℝ)
    norm_num only [Complex.ofReal_ofNat,Complex.ofReal_div,Complex.ofReal_one] at hc
    rw [← hc,← Real.sqrt_eq_rpow]
  simpa only [hp] using hm

/-- The self-dual theta companion has exactly the AGM starting ratio. -/
theorem theta_initial_ratio : alternateSquare 1 = thetaSquare 1 *
    (NNReal.mk (1/Real.sqrt 2) (by positivity)) := by
  have hm := congrArg Complex.re theta_half
  simp only [Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero] at hm
  have h1 := alternate_arithmetic 1 (by norm_num)
  have hh := alternate_arithmetic (1/2) (by norm_num)
  have hg := alternate_geometric (1/2) (by norm_num)
  norm_num only [mul_one,show (2:ℝ)*(1/2)=1 by norm_num,Complex.ofReal_one,one_mul,Complex.ofReal_ofNat] at h1 hh hg
  have hv : (jacobiTheta ((((1/2:ℝ):ℂ))*Complex.I)).re^2 =
      2*(jacobiTheta ((2:ℂ)*Complex.I)).re^2 := by
    rw [hm,mul_pow,Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)]
  have hw : (alternate (1/2))^2 = 2*(jacobiTheta Complex.I).re^2-
      2*(jacobiTheta ((2:ℂ)*Complex.I)).re^2 := by linarith
  have hs : ((alternate 1)^2)^2 = 2*(jacobiTheta ((2:ℂ)*Complex.I)).re^2*
      (2*(jacobiTheta Complex.I).re^2-2*(jacobiTheta ((2:ℂ)*Complex.I)).re^2) := by
    rw [← hw,← hv,← mul_pow,hg]
  have hrel : 2*((alternate 1)^2)^2 = ((jacobiTheta Complex.I).re^2)^2 := by
    have he : (alternate 1)^2 = 2*(jacobiTheta ((2:ℂ)*Complex.I)).re^2-(jacobiTheta Complex.I).re^2 := by linarith
    rw [he] at hs ⊢
    nlinarith [hs]
  apply NNReal.eq
  change (alternate 1)^2 = (jacobiTheta (((1:ℝ):ℂ)*Complex.I)).re^2*(1/Real.sqrt 2)
  simp only [Complex.ofReal_one,one_mul]
  have hroot : Real.sqrt 2 > 0 := by positivity
  have hroot2 : (Real.sqrt 2)^2 = 2 := Real.sq_sqrt (by norm_num)
  have heq : (alternate 1)^2*Real.sqrt 2 = (jacobiTheta Complex.I).re^2 := by
    have hs : ((alternate 1)^2*Real.sqrt 2)^2 = ((jacobiTheta Complex.I).re^2)^2 := by
      rw [mul_pow,hroot2]
      nlinarith [hrel]
    nlinarith [mul_nonneg (sq_nonneg (alternate 1)) hroot.le]
  rw [mul_one_div]
  exact (eq_div_iff hroot.ne').mpr heq

/-- The canonical theta–AGM identity at the self-dual parameter. -/
theorem theta_agm :
    ((NNReal.agm (1:NNReal) (NNReal.mk (1/Real.sqrt 2) (by positivity)):NNReal):ℝ)*
      (jacobiTheta Complex.I).re^2 = 1 := by
  have h := theta_agm_one
  rw [theta_initial_ratio] at h
  have hd := NNReal.agm_mul_distrib (k := thetaSquare 1) (x := (1:NNReal))
    (y := NNReal.mk (1/Real.sqrt 2) (by positivity))
  rw [mul_one] at hd
  rw [hd] at h
  have hc := congrArg (fun x : NNReal => (x:ℝ)) h
  change (thetaSquare 1:ℝ)*(NNReal.agm 1 (NNReal.mk (1/Real.sqrt 2) (by positivity)):ℝ) = 1 at hc
  change (jacobiTheta (((1:ℝ):ℂ)*Complex.I)).re^2*(NNReal.agm 1 (NNReal.mk (1/Real.sqrt 2) (by positivity)):ℝ) = 1 at hc
  simp only [Complex.ofReal_one,one_mul] at hc
  simpa only [mul_comm] using hc

#print axioms theta_mean_step
#print axioms theta_agm_sequences
#print axioms theta_agm_one
#print axioms theta_initial_ratio
#print axioms theta_agm

end Plouffe.Proofs.Gamma.ThetaAGM
