/-
Copyright (c) 2026 Patrick Lopatto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Lopatto
-/
module

public import Plouffe.Infrastructure.Series
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Cotangent
public import Mathlib.Tactic.Ring

public section
namespace Plouffe.Proofs.Coth

/-- Complex hyperbolic cotangent partial fractions in the positive real half-plane. -/
theorem cothKernel : Contracts.cothKernel := by
  intro a ha
  have hp : (Real.pi:ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have ha0 : a ≠ 0 := by
    intro h
    simp [h] at ha
  let x : ℂ := a / ((Real.pi:ℂ)*Complex.I)
  let c : ℂ := ((Real.pi:ℂ)*Complex.I)⁻¹
  have hpx : (Real.pi:ℂ)*Complex.I*x = a := by
    dsimp [x]
    field_simp
  have hx : x ∈ Complex.integerComplement := by
    rw [Complex.mem_integerComplement_iff]
    rintro ⟨n,hn⟩
    have h := congrArg Complex.re hpx
    rw [← hn] at h
    simp at h
    linarith
  have he : Complex.exp (2*a) ≠ 1 := by
    intro h
    have hnorm := congrArg norm h
    rw [Complex.norm_exp] at hnorm
    norm_num only [norm_one] at hnorm
    have hpos : 0 < (2*a).re := by simp; linarith
    have := Real.one_lt_exp_iff.mpr hpos
    exact (ne_of_gt this) hnorm
  have hterm : ∀ j : ℕ, c*cotTerm x j =
      2*a/(a^2+(Real.pi:ℂ)^2*((j+1:ℕ):ℂ)^2) := by
    intro j
    let k : ℂ := (j:ℂ)+1
    have hm : x-k ≠ 0 := by
      simpa [k, sub_eq_add_neg] using Complex.integerComplement_add_ne_zero hx (-((j:ℤ)+1))
    have hp' : x+k ≠ 0 := by
      simpa [k] using Complex.integerComplement_add_ne_zero hx ((j:ℤ)+1)
    have hfac : a^2+(Real.pi:ℂ)^2*k^2 = ((Real.pi:ℂ)*Complex.I)^2*((x-k)*(x+k)) := by
      rw [← hpx]
      simp only [mul_pow, Complex.I_sq]
      ring
    have hd : a^2+(Real.pi:ℂ)^2*k^2 ≠ 0 := by
      rw [hfac]
      exact mul_ne_zero (pow_ne_zero _ (mul_ne_zero hp Complex.I_ne_zero)) (mul_ne_zero hm hp')
    simp only [Nat.cast_add, Nat.cast_one]
    change c*cotTerm x j = 2*a/(a^2+(Real.pi:ℂ)^2*k^2)
    rw [cotTerm_identity hx j]
    change c*(2*x*(1/((x+k)*(x-k)))) = 2*a/(a^2+(Real.pi:ℂ)^2*k^2)
    rw [hfac, ← hpx]
    dsimp [c]
    field_simp
  have hscale : c*((Real.pi:ℂ)*Complex.cot (Real.pi*x)-1/x) =
      (Complex.exp (2*a)+1)/(Complex.exp (2*a)-1)-1/a := by
    rw [Complex.cot_pi_eq_exp_ratio]
    have harg : 2*(Real.pi:ℂ)*Complex.I*x = 2*a := by rw [← hpx]; ring
    rw [harg]
    dsimp [c,x]
    field_simp
    simp only [Complex.I_sq]
    ring
  have hs := (summable_cotTerm hx).mul_left c
  have hrep := congrArg (fun z : ℂ => c*z) (cot_series_rep' hx)
  rw [hscale] at hrep
  calc
    (Complex.exp (2*a)+1)/(Complex.exp (2*a)-1)-1/a = c*∑' j : ℕ, cotTerm x j := hrep
    _ = ∑' j : ℕ, c*cotTerm x j := ((summable_cotTerm hx).tsum_mul_left c).symm
    _ = ∑' j : ℕ, 2*a/(a^2+(Real.pi:ℂ)^2*((j+1:ℕ):ℂ)^2) := tsum_congr hterm

#print axioms cothKernel

end Plouffe.Proofs.Coth
