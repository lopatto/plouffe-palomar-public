/-
Copyright (c) 2026 Patrick Lopatto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Lopatto
-/
module

public import Plouffe.Proofs.Gamma.AGMIntegral.Landen

public section
open MeasureTheory Set Filter
open scoped Topology
namespace Plouffe.Proofs.Gamma

private theorem agmKernel_comm (a b : ℝ) : agmKernel a b = agmKernel b a := by
  funext x
  simp only [agmKernel,mul_comm]

private theorem integral_agmKernel_step (a b : NNReal) (ha : 0 < a) (hb : 0 < b) :
    (∫ x : ℝ in Ioi 0, agmKernel (a:ℝ) (b:ℝ) x) =
      ∫ x : ℝ in Ioi 0, agmKernel (NNReal.sqrt (a*b):ℝ) (((a+b)/2:NNReal):ℝ) x := by
  have h := integral_agmKernel_landen (a:ℝ) (b:ℝ) ha hb
  rw [agmKernel_comm ((↑a+↑b)/2) (Real.sqrt ((↑a:ℝ)*↑b))] at h
  simpa using h

private theorem agmSequences_positive (a b : NNReal) (ha : 0 < a) (hb : 0 < b) (n : ℕ) :
    0 < (NNReal.agmSequences a b n).1 ∧ 0 < (NNReal.agmSequences a b n).2 := by
  induction n generalizing a b with
  | zero =>
    simp only [NNReal.agmSequences_zero]
    constructor <;> positivity
  | succ n ih =>
    rw [NNReal.agmSequences_succ]
    apply ih <;> positivity

private theorem integral_agmKernel_iterate (a b : NNReal) (ha : 0 < a) (hb : 0 < b) (n : ℕ) :
    (∫ x : ℝ in Ioi 0, agmKernel (a:ℝ) (b:ℝ) x) =
      ∫ x : ℝ in Ioi 0, agmKernel ((NNReal.agmSequences a b n).1:ℝ)
        ((NNReal.agmSequences a b n).2:ℝ) x := by
  induction n generalizing a b with
  | zero => simpa only [NNReal.agmSequences_zero] using integral_agmKernel_step a b ha hb
  | succ n ih =>
    rw [NNReal.agmSequences_succ]
    exact (integral_agmKernel_step a b ha hb).trans (ih _ _ (by positivity) (by positivity))

/-- The positive symmetric integral evaluates to pi divided by twice the canonical AGM. -/
theorem integral_agmKernel_eq (a b : NNReal) (ha : 0 < a) (hb : 0 < b) :
    (∫ x : ℝ in Ioi 0, agmKernel (a:ℝ) (b:ℝ) x) = Real.pi/(2*(NNReal.agm a b:ℝ)) := by
  have hp (n : ℕ) := agmSequences_positive a b ha hb n
  have hI (n : ℕ) := integral_agmKernel_iterate a b ha hb n
  have hpr (n : ℕ) : (0:ℝ) < ((NNReal.agmSequences a b n).1:ℝ) ∧ (0:ℝ) < ((NNReal.agmSequences a b n).2:ℝ) := by exact_mod_cast hp n
  have hLo (n : ℕ) : Real.pi/(2*((NNReal.agmSequences a b n).2:ℝ)) ≤
      ∫ x : ℝ in Ioi 0, agmKernel (a:ℝ) (b:ℝ) x := by
    rw [← integral_modelKernel ((NNReal.agmSequences a b n).2:ℝ) (hpr n).2,hI n]
    apply integral_mono (modelKernel_integrable _ (hpr n).2).integrableOn
      (agmKernel_integrable _ _ (hpr n).1 (hpr n).2).integrableOn
    exact fun x => model_le_agmKernel _ _ _ x (hpr n).1 (hpr n).2
      (NNReal.agmSequences_fst_le_snd n n) le_rfl
  have hHi (n : ℕ) : (∫ x : ℝ in Ioi 0, agmKernel (a:ℝ) (b:ℝ) x) ≤
      Real.pi/(2*((NNReal.agmSequences a b n).1:ℝ)) := by
    rw [← integral_modelKernel ((NNReal.agmSequences a b n).1:ℝ) (hpr n).1,hI n]
    apply integral_mono (agmKernel_integrable _ _ (hpr n).1 (hpr n).2).integrableOn
      (modelKernel_integrable _ (hpr n).1).integrableOn
    exact fun x => agmKernel_le_model _ _ _ x (hpr n).1 le_rfl
      (NNReal.agmSequences_fst_le_snd n n)
  have hA : 0 < (NNReal.agm a b:ℝ) := NNReal.agm_pos ha hb
  have htf : Tendsto (fun n => ((NNReal.agmSequences a b n).1:ℝ)) atTop (𝓝 (NNReal.agm a b:ℝ)) :=
    (NNReal.continuous_coe.tendsto _).comp NNReal.tendsto_agmSequences_fst_agm
  have hts : Tendsto (fun n => ((NNReal.agmSequences a b n).2:ℝ)) atTop (𝓝 (NNReal.agm a b:ℝ)) :=
    (NNReal.continuous_coe.tendsto _).comp NNReal.tendsto_agmSequences_snd_agm
  have hlf := (tendsto_const_nhds (x := Real.pi)).div (tendsto_const_nhds.mul htf) (by positivity : (2:ℝ)*(NNReal.agm a b:ℝ) ≠ 0)
  have hls := (tendsto_const_nhds (x := Real.pi)).div (tendsto_const_nhds.mul hts) (by positivity : (2:ℝ)*(NNReal.agm a b:ℝ) ≠ 0)
  exact le_antisymm (ge_of_tendsto' hlf hHi) (le_of_tendsto' hls hLo)

/-- A multiplicative form avoids inverses in downstream endpoint calculations. -/
theorem agm_mul_integral (a b : NNReal) (ha : 0 < a) (hb : 0 < b) :
    (NNReal.agm a b:ℝ)*(∫ x : ℝ in Ioi 0, agmKernel (a:ℝ) (b:ℝ) x) = Real.pi/2 := by
  rw [integral_agmKernel_eq a b ha hb]
  have hA : (NNReal.agm a b:ℝ) ≠ 0 := ne_of_gt (NNReal.agm_pos ha hb)
  field_simp

end Plouffe.Proofs.Gamma
