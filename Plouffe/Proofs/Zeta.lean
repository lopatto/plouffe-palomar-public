/-
Copyright (c) 2026 Patrick Lopatto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Lopatto
-/
module

public import Plouffe.Infrastructure.Series
public import Mathlib.Analysis.PSeriesComplex

public section
namespace Plouffe.Proofs.Zeta

/-- Positive successor-index Dirichlet series for native zeta. -/
theorem zetaPositiveSeries : Contracts.zetaPositiveSeries := by
  intro s hs
  have hsN : 1 < s := by omega
  have hsC : 1 < (s : ℂ).re := by
    simpa only [Complex.natCast_re] using
      (show (1:ℝ) < (s:ℝ) by exact_mod_cast hsN)
  have hsum : Summable (fun n : ℕ => 1 / (n:ℂ)^s) := by
    simpa only [Complex.cpow_natCast] using
      (Complex.summable_one_div_nat_cpow (p := (s:ℂ))).2 hsC
  constructor
  · exact (summable_nat_add_iff 1).2 hsum
  · simpa only [Complex.cpow_natCast, Nat.cast_add, Nat.cast_one] using
      (zeta_eq_tsum_one_div_nat_add_one_cpow hsC)

/-- At integers above one native zeta is the complex cast of a real value. -/
theorem zetaReal : Contracts.zetaReal := by
  intro s hs
  obtain ⟨hsum, hz⟩ := zetaPositiveSeries s hs
  apply Complex.ext
  · simp
  · simp only [Complex.ofReal_im]
    rw [hz, Complex.im_tsum hsum]
    have him (j : ℕ) : (1 / ((j+1:ℕ):ℂ)^s).im = 0 := by
      have he : 1 / ((j+1:ℕ):ℂ)^s = ((1 / ((j+1:ℕ):ℝ)^s : ℝ):ℂ) := by
        simp only [Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_pow, Complex.ofReal_natCast]
      rw [he]
      rfl
    simp only [him, tsum_zero]

end Plouffe.Proofs.Zeta
