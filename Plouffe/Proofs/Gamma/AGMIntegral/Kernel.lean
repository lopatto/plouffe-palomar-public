/-
Copyright (c) 2026 Patrick Lopatto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Lopatto
-/
module

public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
public import Mathlib.Analysis.SpecialFunctions.ArithmeticGeometricMean
public import Mathlib.MeasureTheory.Function.JacobianOneDim
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring

public section
open MeasureTheory Set
namespace Plouffe.Proofs.Gamma

/-- The positive symmetric kernel used in Gauss's arithmetic-geometric-mean transformation. -/
@[expose] noncomputable def agmKernel (a b x : ℝ) : ℝ :=
  1 / Real.sqrt ((x^2+a^2)*(x^2+b^2))

/-- The elementary comparison kernel. -/
@[expose] noncomputable def modelKernel (c x : ℝ) : ℝ := 1/(x^2+c^2)

private theorem modelKernel_scale (c x : ℝ) (hc : c ≠ 0) :
    modelKernel c x = (c^2)⁻¹*(1+(c⁻¹*x)^2)⁻¹ := by
  unfold modelKernel
  field_simp
  ring

/-- Absolute integrability of the elementary comparison kernel. -/
theorem modelKernel_integrable (c : ℝ) (hc : 0 < c) : Integrable (modelKernel c) := by
  have h := (integrable_inv_one_add_mul_sq (inv_ne_zero hc.ne')).const_mul ((c^2)⁻¹)
  exact h.congr (Filter.Eventually.of_forall (fun x => (modelKernel_scale c x hc.ne').symm))

/-- Its positive half-line integral is the standard arctangent value. -/
theorem integral_modelKernel (c : ℝ) (hc : 0 < c) :
    (∫ x : ℝ in Ioi 0, modelKernel c x) = Real.pi/(2*c) := by
  calc
    _ = (c^2)⁻¹*(∫ x : ℝ in Ioi 0, (1+(c⁻¹*x)^2)⁻¹) := by
      rw [← integral_const_mul]
      apply setIntegral_congr_fun measurableSet_Ioi
      intro x hx
      exact modelKernel_scale c x hc.ne'
    _ = _ := by
      rw [integral_comp_mul_left_Ioi (fun x : ℝ => (1+x^2)⁻¹) 0 (inv_pos.mpr hc)]
      simp only [mul_zero,inv_inv,smul_eq_mul,integral_Ioi_inv_one_add_sq,Real.arctan_zero,sub_zero]
      field_simp

/-- Pointwise domination by a lower bound on the two positive parameters. -/
theorem agmKernel_le_model (a b c x : ℝ) (hc : 0 < c) (hca : c ≤ a) (hcb : c ≤ b) :
    agmKernel a b x ≤ modelKernel c x := by
  have ha : 0 < a := hc.trans_le hca
  have hb : 0 < b := hc.trans_le hcb
  have hprod : (x^2+c^2)^2 ≤ (x^2+a^2)*(x^2+b^2) := by
    rw [sq (x^2+c^2)]
    exact mul_le_mul (by nlinarith) (by nlinarith) (by positivity) (by positivity)
  have hs : x^2+c^2 ≤ Real.sqrt ((x^2+a^2)*(x^2+b^2)) :=
    Real.le_sqrt_of_sq_le hprod
  exact one_div_le_one_div_of_le (by positivity) hs

/-- The reverse comparison from an upper bound on both positive parameters. -/
theorem model_le_agmKernel (a b c x : ℝ) (ha : 0 < a) (hb : 0 < b)
    (hac : a ≤ c) (hbc : b ≤ c) : modelKernel c x ≤ agmKernel a b x := by
  have hprod : (x^2+a^2)*(x^2+b^2) ≤ (x^2+c^2)^2 := by
    rw [sq (x^2+c^2)]
    exact mul_le_mul (by nlinarith) (by nlinarith) (by positivity) (by positivity)
  have hs : Real.sqrt ((x^2+a^2)*(x^2+b^2)) ≤ x^2+c^2 := by
    simpa only [Real.sqrt_sq (by positivity : 0 ≤ x^2+c^2)] using Real.sqrt_le_sqrt hprod
  exact one_div_le_one_div_of_le (by positivity) hs

/-- The AGM kernel is continuous when both parameters are positive. -/
theorem agmKernel_continuous (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    Continuous (agmKernel a b) := by
  unfold agmKernel
  apply continuous_const.div
  · exact (Real.continuous_sqrt.comp ((continuous_id.pow 2).add continuous_const |>.mul ((continuous_id.pow 2).add continuous_const)))
  · intro x
    exact ne_of_gt (Real.sqrt_pos.mpr (by positivity))

/-- Absolute integrability precedes all comparisons and transformations. -/
theorem agmKernel_integrable (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    Integrable (agmKernel a b) := by
  apply (modelKernel_integrable (min a b) (lt_min ha hb)).mono'
    (agmKernel_continuous a b ha hb).aestronglyMeasurable
  apply Filter.Eventually.of_forall
  intro x
  rw [Real.norm_of_nonneg (by unfold agmKernel; positivity)]
  exact agmKernel_le_model a b (min a b) x (lt_min ha hb) (min_le_left ..) (min_le_right ..)

/-- Evenness gives the half-line/full-line relation after integrability has been established. -/
theorem integral_agmKernel_even (a b : ℝ) :
    (∫ x : ℝ, agmKernel a b x) = 2*(∫ x : ℝ in Ioi 0, agmKernel a b x) := by
  have he : (fun x : ℝ => agmKernel a b |x|) = agmKernel a b := by
    funext x
    simp only [agmKernel,sq_abs]
  simpa only [he] using (integral_comp_abs (f := agmKernel a b))

end Plouffe.Proofs.Gamma
