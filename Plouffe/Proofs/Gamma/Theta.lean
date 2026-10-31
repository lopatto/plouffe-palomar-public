/-
Copyright (c) 2026 Patrick Lopatto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Lopatto
-/
module

public import Mathlib.NumberTheory.ModularForms.JacobiTheta.OneVariable
public import Mathlib.Topology.Algebra.InfiniteSum.Order
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Linarith

public section
namespace Plouffe.Proofs.Gamma

private theorem theta_I_term (j : ℕ) :
    Complex.exp ((Real.pi:ℂ)*Complex.I*((j:ℂ)+1)^2*Complex.I) =
      (Real.exp (-Real.pi*((j:ℝ)+1)^2):ℂ) := by
  rw [Complex.ofReal_exp]
  congr 1
  push_cast
  ring_nf
  simp [Complex.I_sq]
  ring

/-- The positive real Gaussian series underlying the canonical theta constant at i. -/
theorem theta_I_gaussian_hasSum :
    HasSum (fun j : ℕ => Real.exp (-Real.pi*((j:ℝ)+1)^2))
      (((jacobiTheta Complex.I).re-1)/2) := by
  have h := Complex.reCLM.hasSum (hasSum_nat_jacobiTheta (τ := Complex.I) (by norm_num))
  convert h using 1
  · funext j
    rw [theta_I_term]
    rfl
  · simp

/-- Exact real-series representation of the theta constant; no singular-value evaluation is assumed. -/
theorem theta_I_eq_real_gaussian :
    jacobiTheta Complex.I = ((1+2*(∑' j : ℕ, Real.exp (-Real.pi*((j:ℝ)+1)^2)):ℝ):ℂ) := by
  have hterm : (∑' j : ℕ, Complex.exp ((Real.pi:ℂ)*Complex.I*((j:ℂ)+1)^2*Complex.I)) =
      ((∑' j : ℕ, Real.exp (-Real.pi*((j:ℝ)+1)^2)):ℝ) := by
    calc
      _ = ∑' j : ℕ, (Real.exp (-Real.pi*((j:ℝ)+1)^2):ℂ) := tsum_congr theta_I_term
      _ = _ := (Complex.ofReal_tsum _).symm
  rw [jacobiTheta_eq_tsum_nat (by norm_num),hterm]
  push_cast
  rfl

/-- The imaginary-axis theta constant is real. -/
theorem theta_I_im : (jacobiTheta Complex.I).im = 0 := by
  rw [theta_I_eq_real_gaussian]
  exact Complex.ofReal_im _

/-- Strict positivity follows from the convergent positive Gaussian series. -/
theorem one_lt_theta_I_re : 1 < (jacobiTheta Complex.I).re := by
  have hpos := theta_I_gaussian_hasSum.summable.tsum_pos (fun j => (Real.exp_pos _).le) 0 (Real.exp_pos _)
  rw [theta_I_gaussian_hasSum.tsum_eq] at hpos
  linarith


end Plouffe.Proofs.Gamma
