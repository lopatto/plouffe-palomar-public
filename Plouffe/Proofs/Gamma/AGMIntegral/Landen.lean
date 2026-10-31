/-
Copyright (c) 2026 Patrick Lopatto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Lopatto
-/
module

public import Plouffe.Proofs.Gamma.AGMIntegral.Kernel

public section
open MeasureTheory Set
namespace Plouffe.Proofs.Gamma

private noncomputable def landenMap (c x : ℝ) : ℝ := (x-c/x)/2
private noncomputable def landenDeriv (c x : ℝ) : ℝ := (1+c/x^2)/2

private theorem landenMap_hasDeriv (c x : ℝ) (hx : 0 < x) :
    HasDerivAt (landenMap c) (landenDeriv c x) x := by
  have h := ((hasDerivAt_id x).sub ((hasDerivAt_const x c).div (hasDerivAt_id x) hx.ne')).div_const 2
  change HasDerivAt (fun z : ℝ => (z-c/z)/2) ((1+c/x^2)/2) x
  simpa [neg_div] using h

private theorem landenDeriv_pos (c x : ℝ) (hc : 0 < c) (hx : 0 < x) :
    0 < landenDeriv c x := by unfold landenDeriv; positivity

private theorem landenMap_inj (c : ℝ) (hc : 0 < c) : InjOn (landenMap c) (Ioi 0) := by
  intro x hx y hy h
  change 0 < x at hx
  change 0 < y at hy
  dsimp [landenMap] at h
  have hx0 : x ≠ 0 := ne_of_gt hx
  have hy0 : y ≠ 0 := ne_of_gt hy
  have he : (x-y)*(x*y+c) = 0 := by
    field_simp at h
    nlinarith
  exact sub_eq_zero.mp ((mul_eq_zero.mp he).resolve_right (ne_of_gt (by positivity)))

private theorem landenMap_image (c : ℝ) (hc : 0 < c) : landenMap c '' (Ioi 0) = univ := by
  apply eq_univ_of_forall
  intro y
  let r := Real.sqrt (y^2+c)
  have hr : r^2 = y^2+c := Real.sq_sqrt (by positivity)
  have hxr : 0 < y+r := by
    have h := Real.neg_sqrt_lt_of_sq_lt (show y^2 < y^2+c by linarith)
    dsimp [r]
    linarith
  refine ⟨y+r,hxr,?_⟩
  unfold landenMap
  apply (div_eq_iff (by norm_num : (2:ℝ) ≠ 0)).mpr
  field_simp
  nlinarith

private theorem landen_sqrt (a b x : ℝ) (ha : 0 < a) (hb : 0 < b) (hx : 0 < x) :
    Real.sqrt (((landenMap (a*b) x)^2+((a+b)/2)^2)*
      ((landenMap (a*b) x)^2+(Real.sqrt (a*b))^2)) =
      ((x^2+a*b)/(4*x^2))*Real.sqrt ((x^2+a^2)*(x^2+b^2)) := by
  have hab : 0 < a*b := mul_pos ha hb
  have hD : 0 < (x^2+a^2)*(x^2+b^2) := by positivity
  have hsq := Real.sq_sqrt hD.le
  have hsab := Real.sq_sqrt hab.le
  apply (Real.sqrt_eq_iff_eq_sq (by positivity) (by positivity)).mpr
  unfold landenMap
  rw [hsab,mul_pow,hsq]
  field_simp
  ring

private theorem landen_kernel (a b x : ℝ) (ha : 0 < a) (hb : 0 < b) (hx : 0 < x) :
    landenDeriv (a*b) x * agmKernel ((a+b)/2) (Real.sqrt (a*b)) (landenMap (a*b) x) =
      2*agmKernel a b x := by
  have hD : 0 < Real.sqrt ((x^2+a^2)*(x^2+b^2)) := Real.sqrt_pos.mpr (by positivity)
  unfold agmKernel
  rw [landen_sqrt a b x ha hb hx]
  unfold landenDeriv
  field_simp
  ring

/-- Gauss's change of variable preserves the positive half-line AGM integral. -/
theorem integral_agmKernel_landen (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    (∫ x : ℝ in Ioi 0, agmKernel a b x) =
      ∫ x : ℝ in Ioi 0, agmKernel ((a+b)/2) (Real.sqrt (a*b)) x := by
  have hab : 0 < a*b := mul_pos ha hb
  have hi := agmKernel_integrable a b ha hb
  have hj := agmKernel_integrable ((a+b)/2) (Real.sqrt (a*b)) (by positivity) (Real.sqrt_pos.mpr hab)
  have h := integral_image_eq_integral_abs_deriv_smul measurableSet_Ioi
    (fun x hx => (landenMap_hasDeriv (a*b) x hx).hasDerivWithinAt)
    (landenMap_inj (a*b) hab) (agmKernel ((a+b)/2) (Real.sqrt (a*b)))
  rw [landenMap_image (a*b) hab,Measure.restrict_univ,integral_agmKernel_even] at h
  have he : (∫ x : ℝ in Ioi 0,
      |landenDeriv (a*b) x| • agmKernel ((a+b)/2) (Real.sqrt (a*b)) (landenMap (a*b) x)) =
      2*(∫ x : ℝ in Ioi 0, agmKernel a b x) := by
    rw [← integral_const_mul]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro x hx
    change |landenDeriv (a*b) x| • agmKernel ((a+b)/2) (Real.sqrt (a*b)) (landenMap (a*b) x) = 2*agmKernel a b x
    rw [abs_of_pos (landenDeriv_pos (a*b) x hab hx),smul_eq_mul]
    exact landen_kernel a b x ha hb hx
  rw [he] at h
  linarith

end Plouffe.Proofs.Gamma
