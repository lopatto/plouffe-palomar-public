/-
Copyright (c) 2026 Patrick Lopatto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Lopatto
-/
module

public import Plouffe.Reduction

public section
namespace Plouffe.Examples
private theorem bp0 : bernoulli' 0 = (1:ℚ) := by
  rw [bernoulli'_def]
  norm_num [Nat.choose,Finset.sum_range_succ]
private theorem bp1 : bernoulli' 1 = (1/2:ℚ) := by
  rw [bernoulli'_def]
  norm_num [Nat.choose,Finset.sum_range_succ,bp0]
private theorem bp2 : bernoulli' 2 = (1/6:ℚ) := by
  rw [bernoulli'_def]
  norm_num [Nat.choose,Finset.sum_range_succ,bp0,bp1]
private theorem bp3 : bernoulli' 3 = (0:ℚ) := by
  rw [bernoulli'_def]
  norm_num [Nat.choose,Finset.sum_range_succ,bp0,bp1,bp2]
private theorem bp4 : bernoulli' 4 = (-1/30:ℚ) := by
  rw [bernoulli'_def]
  norm_num [Nat.choose,Finset.sum_range_succ,bp0,bp1,bp2,bp3]
private theorem bp5 : bernoulli' 5 = (0:ℚ) := by
  rw [bernoulli'_def]
  norm_num [Nat.choose,Finset.sum_range_succ,bp0,bp1,bp2,bp3,bp4]
private theorem bp6 : bernoulli' 6 = (1/42:ℚ) := by
  rw [bernoulli'_def]
  norm_num [Nat.choose,Finset.sum_range_succ,bp0,bp1,bp2,bp3,bp4,bp5]
private theorem bp7 : bernoulli' 7 = (0:ℚ) := by
  rw [bernoulli'_def]
  norm_num [Nat.choose,Finset.sum_range_succ,bp0,bp1,bp2,bp3,bp4,bp5,bp6]
private theorem bp8 : bernoulli' 8 = (-1/30:ℚ) := by
  rw [bernoulli'_def]
  norm_num [Nat.choose,Finset.sum_range_succ,bp0,bp1,bp2,bp3,bp4,bp5,bp6,bp7]
private theorem b0 : bernoulli 0 = (1:ℚ) := by norm_num [bernoulli,bp0]
private theorem b2 : bernoulli 2 = (1/6:ℚ) := by norm_num [bernoulli,bp2]
private theorem b4 : bernoulli 4 = (-1/30:ℚ) := by norm_num [bernoulli,bp4]
private theorem b6 : bernoulli 6 = (1/42:ℚ) := by norm_num [bernoulli,bp6]
private theorem b8 : bernoulli 8 = (-1/30:ℚ) := by norm_num [bernoulli,bp8]

/-- Numerical corollary in §1, conditional only on the general family package. -/
theorem pi3 (h : Principal) : Real.pi^3 = 720*S 3 1-900*S 3 2+180*S 3 4 := by
  have ht := h.oddPi 1 (by norm_num)
  norm_num [D,E,K,F,G,H,b0,b2,b4,b6,b8,Finset.sum_range_succ] at ht
  exact ht

/-- Numerical corollary in §1, conditional only on the general family package. -/
theorem pi5 (h : Principal) : Real.pi^5 = 7056*S 5 1-6993*S 5 2-63*S 5 4 := by
  have ht := h.evenPi 1 (by norm_num)
  norm_num [D,E,K,F,G,H,b0,b2,b4,b6,b8,Finset.sum_range_succ] at ht
  exact ht

/-- Numerical corollary in §1, conditional only on the general family package. -/
theorem pi7 (h : Principal) : Real.pi^7 = (907200/13:ℝ)*S 7 1-70875*S 7 2+(14175/13:ℝ)*S 7 4 := by
  have ht := h.oddPi 2 (by norm_num)
  norm_num [D,E,K,F,G,H,b0,b2,b4,b6,b8,Finset.sum_range_succ] at ht
  exact ht

/-- Numerical corollary in §1, conditional only on the general family package. -/
theorem zeta3 (h : Principal) : riemannZeta (3:ℂ) = ((28*S 3 1-37*S 3 2+7*S 3 4:ℝ):ℂ) := by
  have ht := h.oddZeta 1 (by norm_num)
  norm_num [D,E,K,F,G,H,b0,b2,b4,b6,b8,Finset.sum_range_succ] at ht
  convert ht using 1; push_cast; ring

/-- Numerical corollary in §1, conditional only on the general family package. -/
theorem zeta5 (h : Principal) : riemannZeta (5:ℂ) = ((24*S 5 1-(259/10:ℝ)*S 5 2-(1/10:ℝ)*S 5 4:ℝ):ℂ) := by
  have ht := h.evenZeta 1 (by norm_num)
  norm_num [D,E,K,F,G,H,b0,b2,b4,b6,b8,Finset.sum_range_succ] at ht
  convert ht using 1; push_cast; ring

/-- Numerical corollary in §1, conditional only on the general family package. -/
theorem zeta7 (h : Principal) : riemannZeta (7:ℂ) = (((304/13:ℝ)*S 7 1-(103/4:ℝ)*S 7 2+(19/52:ℝ)*S 7 4:ℝ):ℂ) := by
  have ht := h.oddZeta 2 (by norm_num)
  norm_num [D,E,K,F,G,H,b0,b2,b4,b6,b8,Finset.sum_range_succ] at ht
  convert ht using 1; push_cast; ring

end Plouffe.Examples
