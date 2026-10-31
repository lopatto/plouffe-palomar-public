/-
Copyright (c) 2026 Patrick Lopatto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Lopatto
-/
module

public import Plouffe.Proofs.Ramanujan.Bernoulli

public section
namespace Plouffe.Proofs.Ramanujan

/-- Ramanujan's transformation in the positive-real-part half-plane. -/
theorem ramanujanComplex : Contracts.ramanujanComplex := by
  intro n a b hn ha hb hab
  have ha0 : a ≠ 0 := by intro h; simp [h] at ha
  have hb0 : b ≠ 0 := by intro h; simp [h] at hb
  have hA := lambert_double_sum n a b hn ha hb hab
  have hB := lambert_double_sum n b a hn hb ha (by rw [mul_comm,hab])
  have hD := double_difference n a b hn ha hb
  have hBern := bernoulli_convolution n a b ha0 hb0 hab
  have hneg : ((-b)^n)⁻¹ = (-1:ℂ)^n*(b^n)⁻¹ := by
    rw [show -b = (-1:ℂ)*b by ring,mul_pow,mul_inv_rev]
    simp only [← inv_pow,inv_neg,inv_one]
    ring
  rw [hneg,hA,hB]
  linear_combination hD+hBern

#print axioms ramanujanComplex

end Plouffe.Proofs.Ramanujan
