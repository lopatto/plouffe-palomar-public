/-
Copyright (c) 2026 Patrick Lopatto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Lopatto
-/
module

public import Plouffe.Contracts
public import Mathlib.Analysis.PSeries
public import Mathlib.Analysis.Normed.Ring.InfiniteSum

public section
namespace Plouffe.Proofs.Double

private theorem term_bound (n k l : ℕ) (a b : ℂ) (ha : 0 < a.re) (hb : 0 < b.re) :
    ‖1 / (((k+1:ℕ):ℂ)^(2*n) * (a*((k+1:ℕ):ℂ)^2+b*((l+1:ℕ):ℂ)^2))‖ ≤
      (1/b.re)*((1/((k+1:ℕ):ℝ)^(2*n))*(1/((l+1:ℕ):ℝ)^2)) := by
  have hRe : (a*((k+1:ℕ):ℂ)^2+b*((l+1:ℕ):ℂ)^2).re =
      a.re*((k+1:ℕ):ℝ)^2+b.re*((l+1:ℕ):ℝ)^2 := by
    simp [Complex.add_re, Complex.mul_re, pow_two]
  have hnorm : b.re*((l+1:ℕ):ℝ)^2 ≤ ‖a*((k+1:ℕ):ℂ)^2+b*((l+1:ℕ):ℂ)^2‖ := by
    calc
      _ ≤ (a*((k+1:ℕ):ℂ)^2+b*((l+1:ℕ):ℂ)^2).re := by
        rw [hRe]
        exact le_add_of_nonneg_left (mul_nonneg ha.le (sq_nonneg _))
      _ ≤ _ := Complex.re_le_norm _
  have hl : (0:ℝ) < ((l+1:ℕ):ℝ)^2 := pow_pos (by positivity) _
  have hk : (0:ℝ) < ((k+1:ℕ):ℝ)^(2*n) := pow_pos (by positivity) _
  rw [norm_div, norm_one, norm_mul, norm_pow, Complex.norm_natCast]
  calc
    _ ≤ 1/(((k+1:ℕ):ℝ)^(2*n)*(b.re*((l+1:ℕ):ℝ)^2)) :=
      one_div_le_one_div_of_le (mul_pos hk (mul_pos hb hl)) (mul_le_mul_of_nonneg_left hnorm hk.le)
    _ = _ := by simp only [one_div, mul_inv_rev]; ring

/-- Absolute convergence of the Ramanujan double-series kernel in the right half-plane. -/
theorem doubleSummable : Contracts.doubleSummable := by
  intro n a b hn ha hb
  have hf : Summable (fun k : ℕ => 1/((k+1:ℕ):ℝ)^(2*n)) :=
    (summable_nat_add_iff 1).mpr (Real.summable_one_div_nat_pow.mpr (by omega))
  have hg : Summable (fun l : ℕ => 1/((l+1:ℕ):ℝ)^2) :=
    (summable_nat_add_iff 1).mpr (Real.summable_one_div_nat_pow.mpr (by norm_num))
  have hp := (hf.mul_of_nonneg hg (by intro k; positivity) (by intro l; positivity)).mul_left (1/b.re)
  apply Summable.of_norm
  apply hp.of_nonneg_of_le (fun _ => norm_nonneg _)
  intro kl
  exact term_bound n kl.1 kl.2 a b ha hb


end Plouffe.Proofs.Double
