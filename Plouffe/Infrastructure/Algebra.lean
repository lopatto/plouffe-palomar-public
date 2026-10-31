/-
Copyright (c) 2026 Patrick Lopatto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Lopatto
-/
module

public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.LinearCombination

public section
namespace Plouffe.Algebra

/-- Elimination before substituting the paper's coefficients. -/
theorem odd_solve (q f g d a b c P z : ℝ) (hd : d ≠ 0)
    (hdef : 2*d = q*((q+1)*f-g))
    (hc : z+2*b = -f*q*P) (hu : d*P = q*a-(q+1)*b+c) :
    P = q/d*a-(q+1)/d*b+1/d*c ∧
    z = -f*q^2/d*a+g*q/d*b-f*q/d*c := by
  constructor
  · field_simp
    nlinarith [hu]
  · field_simp
    linear_combination d*hc - f*q*hu - b*hdef

/-- Elimination for the second branch. -/
theorem even_solve (p q g k e a b c P z : ℝ) (he : e ≠ 0) (hp : p-1 ≠ 0)
    (hu : e*P = -p*a+2*k*(2*p-q+1)*b+(1-4*k)*c)
    (hz : z*(p-1) = -2*p*a+2*c-p*P*g) :
    P = -p/e*a+2*k*(2*p-q+1)/e*b+(1-4*k)/e*c ∧
    z = -(p*(2*e-p*g))/((p-1)*e)*a -
      (2*p*g*k*(2*p-q+1))/((p-1)*e)*b -
      (p*g*(1-4*k)-2*e)/((p-1)*e)*c := by
  constructor
  · field_simp
    nlinarith [hu]
  · field_simp
    linear_combination e*hz - p*g*hu

end Plouffe.Algebra
