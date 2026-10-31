/-
Copyright (c) 2026 Patrick Lopatto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Lopatto
-/
module

public import Plouffe.Proofs.Gamma.AGMIntegral.Evaluation
public import Mathlib.Analysis.SpecialFunctions.Sqrt

public section
open MeasureTheory Set
namespace Plouffe.Proofs.Gamma

private noncomputable def lemniscaticMap (t : ℝ) : ℝ := t/Real.sqrt (1-t^2)
private noncomputable def lemniscaticDeriv (t : ℝ) : ℝ := 1/(Real.sqrt (1-t^2))^3

private theorem lemniscatic_positive (t : ℝ) (ht : t ∈ Ioo (0:ℝ) 1) : 0 < 1-t^2 := by
  nlinarith [ht.1,ht.2]

private theorem lemniscaticMap_hasDeriv (t : ℝ) (ht : t ∈ Ioo (0:ℝ) 1) :
    HasDerivAt lemniscaticMap (lemniscaticDeriv t) t := by
  have hp := lemniscatic_positive t ht
  have hs := Real.sq_sqrt hp.le
  have hd := ((hasDerivAt_const t (1:ℝ)).sub (hasDerivAt_pow 2 t)).sqrt (ne_of_gt hp)
  have h := (hasDerivAt_id t).div hd (ne_of_gt (Real.sqrt_pos.mpr hp))
  change HasDerivAt (fun x : ℝ => x/Real.sqrt (1-x^2)) (1/(Real.sqrt (1-t^2))^3) t
  apply h.congr_deriv
  simp only [id_eq,Pi.sub_apply,Nat.cast_ofNat,Nat.reduceSub,pow_one,zero_sub,one_mul]
  field_simp
  nlinarith [hs]

private theorem lemniscaticMap_inj : InjOn lemniscaticMap (Ioo (0:ℝ) 1) := by
  intro x hx y hy h
  have hpx := lemniscatic_positive x hx
  have hpy := lemniscatic_positive y hy
  have hsx := Real.sq_sqrt hpx.le
  have hsy := Real.sq_sqrt hpy.le
  unfold lemniscaticMap at h
  have he : x*Real.sqrt (1-y^2) = y*Real.sqrt (1-x^2) := (div_eq_div_iff (by positivity) (by positivity)).mp h
  have he2 := congrArg (fun z : ℝ => z^2) he
  rw [mul_pow,mul_pow,hsx,hsy] at he2
  nlinarith [hx.1,hy.1]

private theorem lemniscaticMap_image : lemniscaticMap '' (Ioo (0:ℝ) 1) = Ioi 0 := by
  apply Subset.antisymm
  · rintro _ ⟨t,ht,rfl⟩
    exact div_pos ht.1 (Real.sqrt_pos.mpr (lemniscatic_positive t ht))
  · intro x hx
    change 0 < x at hx
    let s := Real.sqrt (1+x^2)
    have hs : 0 < s := Real.sqrt_pos.mpr (by positivity)
    have hs2 : s^2 = 1+x^2 := Real.sq_sqrt (by positivity)
    have hxs : x < s := Real.lt_sqrt_of_sq_lt (by linarith)
    have ht : x/s ∈ Ioo (0:ℝ) 1 := ⟨div_pos hx hs,(div_lt_one hs).mpr hxs⟩
    have hroot : Real.sqrt (1-(x/s)^2) = 1/s := by
      apply (Real.sqrt_eq_iff_eq_sq (lemniscatic_positive (x/s) ht).le (by positivity)).mpr
      field_simp
      nlinarith [hs2]
    refine ⟨x/s,ht,?_⟩
    unfold lemniscaticMap
    rw [hroot]
    field_simp

private theorem lemniscatic_kernel (t : ℝ) (ht : t ∈ Ioo (0:ℝ) 1) :
    lemniscaticDeriv t * agmKernel 1 (1/Real.sqrt 2) (lemniscaticMap t) =
      Real.sqrt 2*(1/Real.sqrt (1-t^4)) := by
  have hp := lemniscatic_positive t ht
  have hs : 0 < Real.sqrt (1-t^2) := Real.sqrt_pos.mpr hp
  have hs2 := Real.sq_sqrt hp.le
  have hr : 0 < Real.sqrt 2 := by positivity
  have hr2 : (Real.sqrt 2)^2 = 2 := Real.sq_sqrt (by norm_num)
  have h4 : 0 < 1-t^4 := by nlinarith [sq_pos_of_pos hp,ht.1,ht.2]
  have hf : 0 < Real.sqrt (1-t^4) := Real.sqrt_pos.mpr h4
  have hf2 := Real.sq_sqrt h4.le
  have hroot : Real.sqrt (((lemniscaticMap t)^2+(1:ℝ)^2)*
      ((lemniscaticMap t)^2+(1/Real.sqrt 2)^2)) =
      Real.sqrt (1-t^4)/(Real.sqrt 2*(Real.sqrt (1-t^2))^3) := by
    apply (Real.sqrt_eq_iff_eq_sq (by positivity) (by positivity)).mpr
    unfold lemniscaticMap
    simp only [div_pow,mul_pow,hf2,hr2]
    rw [show (Real.sqrt (1-t^2)^3)^2 = (Real.sqrt (1-t^2)^2)^3 by ring,hs2]
    field_simp
    ring
  unfold agmKernel
  rw [hroot]
  unfold lemniscaticDeriv
  field_simp

/-- The quartic substitution links the symmetric positive-half-line integral to the lemniscatic one. -/
theorem integral_agmKernel_lemniscatic
    (hJ : IntervalIntegrable (fun x : ℝ => 1/Real.sqrt (1-x^4)) volume 0 1) :
    (∫ x : ℝ in Ioi 0, agmKernel 1 (1/Real.sqrt 2) x) =
      Real.sqrt 2*(∫ x : ℝ in (0:ℝ)..1, 1/Real.sqrt (1-x^4)) := by
  have hi := agmKernel_integrable 1 (1/Real.sqrt 2) (by norm_num) (by positivity)
  have hJ_integrable : IntegrableOn (fun x : ℝ => 1/Real.sqrt (1-x^4)) (Ioo 0 1) :=
    hJ.1.mono_set Ioo_subset_Ioc_self
  have h := integral_image_eq_integral_abs_deriv_smul measurableSet_Ioo
    (fun t ht => (lemniscaticMap_hasDeriv t ht).hasDerivWithinAt)
    lemniscaticMap_inj (agmKernel 1 (1/Real.sqrt 2))
  rw [lemniscaticMap_image] at h
  calc
    _ = ∫ t : ℝ in Ioo (0:ℝ) 1,
        lemniscaticDeriv t*agmKernel 1 (1/Real.sqrt 2) (lemniscaticMap t) := by
      rw [h]
      apply setIntegral_congr_fun measurableSet_Ioo
      intro t ht
      change |lemniscaticDeriv t| • _ = _
      rw [abs_of_pos (by unfold lemniscaticDeriv; exact one_div_pos.mpr (pow_pos (Real.sqrt_pos.mpr (lemniscatic_positive t ht)) _)),smul_eq_mul]
    _ = ∫ t : ℝ in Ioo (0:ℝ) 1, Real.sqrt 2*(1/Real.sqrt (1-t^4)) := by
      apply setIntegral_congr_fun measurableSet_Ioo
      intro t ht
      exact lemniscatic_kernel t ht
    _ = _ := by rw [integral_const_mul,← integral_Ioc_eq_integral_Ioo,← intervalIntegral.integral_of_le (by norm_num : (0:ℝ) ≤ 1)]

/-- The canonical AGM at the lemniscatic parameter is the reciprocal period constant. -/
theorem agm_lemniscatic
    (hJ : IntervalIntegrable (fun x : ℝ => 1/Real.sqrt (1-x^4)) volume 0 1) :
    ((NNReal.agm (1:NNReal) (⟨1/Real.sqrt 2,by positivity⟩:NNReal):NNReal):ℝ)*
      (∫ x : ℝ in (0:ℝ)..1, 1/Real.sqrt (1-x^4)) = Real.pi/(2*Real.sqrt 2) := by
  have h := agm_mul_integral (1:NNReal) (⟨1/Real.sqrt 2,by positivity⟩:NNReal)
    (by norm_num) (by exact_mod_cast (show (0:ℝ) < 1/Real.sqrt 2 by positivity))
  change ((NNReal.agm (1:NNReal) (⟨1/Real.sqrt 2,by positivity⟩:NNReal):NNReal):ℝ)*
    (∫ x : ℝ in Ioi 0, agmKernel 1 (1/Real.sqrt 2) x) = Real.pi/2 at h
  rw [integral_agmKernel_lemniscatic hJ] at h
  apply (eq_div_iff (by positivity : (2:ℝ)*Real.sqrt 2 ≠ 0)).mpr
  nlinarith

end Plouffe.Proofs.Gamma
