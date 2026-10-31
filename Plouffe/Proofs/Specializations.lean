/-
Copyright (c) 2026 Patrick Lopatto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Lopatto
-/
module

public import Plouffe.Proofs.Ramanujan
public import Plouffe.Proofs.Series
public import Plouffe.Proofs.Zeta
public import Plouffe.Proofs.Elementary

public section
namespace Plouffe.Proofs.Specializations

/-- Restrict the proved complex transformation to the manuscript's positive real parameters. -/
theorem ramanujanReal : Contracts.ramanujanReal := by
  intro n a b hn ha hb hab
  have h := Ramanujan.ramanujanComplex n (a:ℂ) (b:ℂ) hn
    (by simpa using ha) (by simpa using hb) (by exact_mod_cast hab)
  rw [Series.lambertReal n a ha,Series.lambertReal n b hb] at h
  exact h

private theorem diagonal_polynomial (n : ℕ) (a : ℂ) :
    (∑ k ∈ Finset.range (n+2), (((-1:ℚ)^k*bernoulli (2*k)*bernoulli (2*n+2-2*k)/
      ((Nat.factorial (2*k):ℚ)*(Nat.factorial (2*n+2-2*k):ℚ))) : ℂ)*a^(n+1-k)*a^k) =
      a^(n+1)*(F n:ℂ) := by
  unfold F
  push_cast
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  have hk' : k ≤ n+1 := by have := Finset.mem_range.mp hk; omega
  have hp : a^(n+1-k)*a^k = a^(n+1) := by rw [← pow_add,Nat.sub_add_cancel hk']
  calc
    _ = (((-1:ℚ)^k*bernoulli (2*k)*bernoulli (2*n+2-2*k)/
      ((Nat.factorial (2*k):ℚ)*(Nat.factorial (2*n+2-2*k):ℚ))) : ℂ)*(a^(n+1-k)*a^k) := by push_cast; ring
    _ = _ := by rw [hp]; push_cast; ring

/-- Equal positive parameters factor the finite convolution into F. -/
theorem center : Contracts.center := by
  intro n hn
  have h := ramanujanReal n Real.pi Real.pi hn Real.pi_pos Real.pi_pos (by ring)
  have hp : 2*Real.pi/Real.pi = (2:ℝ) := by field_simp
  rw [hp,diagonal_polynomial] at h
  linear_combination h

private theorem inverse_neg_pow (b : ℂ) (n : ℕ) :
    ((-b)^n)⁻¹ = (-1:ℂ)^n*(b^n)⁻¹ := by
  rw [show -b = (-1:ℂ)*b by ring,mul_pow,mul_inv_rev]
  simp only [← inv_pow,inv_neg,inv_one]
  ring

/-- The centered identity for positive odd n, after honest restriction to real parts. -/
theorem oddCenter : Contracts.oddCenter := by
  intro n hn hodd
  have h := center n hn
  have hp : (Real.pi:ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  rw [inverse_neg_pow, hodd.neg_one_pow] at h
  have hmul : riemannZeta ((2*n+1:ℕ):ℂ)+2*(S (2*n+1) 2:ℂ) =
      -(4:ℂ)^n*(Real.pi:ℂ)^(2*n+1)*(F n:ℂ) := by
    have hpow : (Real.pi:ℂ)^n*(Real.pi:ℂ)^(n+1) = (Real.pi:ℂ)^(2*n+1) := by
      rw [← pow_add,show n+(n+1)=2*n+1 by omega]
    have hc : (Real.pi:ℂ)^n*((Real.pi:ℂ)^n)⁻¹ = 1 := mul_inv_cancel₀ (pow_ne_zero _ hp)
    have hh := congrArg (fun z : ℂ => (Real.pi:ℂ)^n*z) h
    have hh' : 2*((Real.pi:ℂ)^n*((Real.pi:ℂ)^n)⁻¹)*
        (riemannZeta ((2*n+1:ℕ):ℂ)/2+(S (2*n+1) 2:ℂ)) =
        -(4:ℂ)^n*((Real.pi:ℂ)^n*(Real.pi:ℂ)^(n+1))*(F n:ℂ) := by linear_combination hh
    rw [hc,hpow] at hh'
    linear_combination hh'
  have h4 : (4:ℂ)^n = (((4:ℝ)^n:ℝ):ℂ) := by norm_cast
  rw [h4] at hmul
  simpa [← Complex.ofReal_pow,Complex.mul_re] using congrArg Complex.re hmul


private theorem scaled_polynomial (n : ℕ) (a : ℂ) :
    (∑ k ∈ Finset.range (n+2), (((-1:ℚ)^k*bernoulli (2*k)*bernoulli (2*n+2-2*k)/
      ((Nat.factorial (2*k):ℚ)*(Nat.factorial (2*n+2-2*k):ℚ))) : ℂ)*a^(n+1-k)*(4*a)^k) =
      a^(n+1)*(G n:ℂ) := by
  unfold G
  push_cast
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  have hk' : k ≤ n+1 := by have := Finset.mem_range.mp hk; omega
  have hp : a^(n+1-k)*a^k = a^(n+1) := by rw [← pow_add,Nat.sub_add_cancel hk']
  have hsign : (-1:ℂ)^k*(4:ℂ)^k = (-4:ℂ)^k := by rw [← mul_pow]; norm_num
  have ht : (-1:ℂ)^k*a^(n+1-k)*(4*a)^k = (-4:ℂ)^k*a^(n+1) := by
    calc
      _ = ((-1:ℂ)^k*(4:ℂ)^k)*(a^(n+1-k)*a^k) := by rw [mul_pow]; ring
      _ = _ := by rw [hsign,hp]
  linear_combination ((bernoulli (2*k):ℂ)*(bernoulli (2*n+2-2*k):ℂ)/
    ((Nat.factorial (2*k):ℂ)*(Nat.factorial (2*n+2-2*k):ℂ)))*ht

private theorem two_scale_complex (n : ℕ) (hn : 1 ≤ n) :
    ((4:ℂ)^n-(-1:ℂ)^n)*riemannZeta ((2*n+1:ℕ):ℂ) =
      -2*(4:ℂ)^n*(S (2*n+1) 1:ℂ)+2*(-1:ℂ)^n*(S (2*n+1) 4:ℂ)-
      (4:ℂ)^n*(Real.pi:ℂ)^(2*n+1)*(G n:ℂ) := by
  have h := ramanujanReal n (Real.pi/2) (2*Real.pi) hn (by positivity) (by positivity) (by ring)
  have hS1 : 2*(Real.pi/2)/Real.pi = (1:ℝ) := by field_simp
  have hS4 : 2*(2*Real.pi)/Real.pi = (4:ℝ) := by field_simp; norm_num
  rw [hS1,hS4] at h
  push_cast at h
  have he : 2*(Real.pi:ℂ) = 4*((Real.pi:ℂ)/2) := by ring
  have hpoly := scaled_polynomial n ((Real.pi:ℂ)/2)
  rw [← he] at hpoly
  push_cast at hpoly
  rw [hpoly] at h
  have hp : (Real.pi:ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hA : ((Real.pi:ℂ)/2) ≠ 0 := div_ne_zero hp (by norm_num)
  have hB : 2*(Real.pi:ℂ) ≠ 0 := mul_ne_zero (by norm_num) hp
  have hratio : (2*(Real.pi:ℂ))^n*(((Real.pi:ℂ)/2)^n)⁻¹ = (4:ℂ)^n := by
    rw [he,mul_pow]
    field_simp
  have hneg : (2*(Real.pi:ℂ))^n*((-(2*(Real.pi:ℂ)))^n)⁻¹ = (-1:ℂ)^n := by
    rw [inverse_neg_pow]
    calc
      _ = (-1:ℂ)^n*((2*(Real.pi:ℂ))^n*((2*(Real.pi:ℂ))^n)⁻¹) := by ring
      _ = _ := by rw [mul_inv_cancel₀ (pow_ne_zero _ hB)]; ring
  have hcross : 2*(2*(Real.pi:ℂ))^n*(4:ℂ)^n*((Real.pi:ℂ)/2)^(n+1) =
      (4:ℂ)^n*(Real.pi:ℂ)^(2*n+1) := by
    have hab : (2*(Real.pi:ℂ))*((Real.pi:ℂ)/2) = (Real.pi:ℂ)^2 := by ring
    rw [pow_succ]
    calc
      _ = (4:ℂ)^n*(2*((Real.pi:ℂ)/2))*(((2*(Real.pi:ℂ))*((Real.pi:ℂ)/2))^n) := by
        simp only [mul_pow]
        ring
      _ = _ := by rw [hab,← pow_mul,pow_succ]; ring
  have hh : 2*((2*(Real.pi:ℂ))^n*(((Real.pi:ℂ)/2)^n)⁻¹)*
      (riemannZeta ((2*n+1:ℕ):ℂ)/2+(S (2*n+1) 1:ℂ)) =
      2*((2*(Real.pi:ℂ))^n*((-(2*(Real.pi:ℂ)))^n)⁻¹)*
        (riemannZeta ((2*n+1:ℕ):ℂ)/2+(S (2*n+1) 4:ℂ))-
      (2*(2*(Real.pi:ℂ))^n*(4:ℂ)^n*((Real.pi:ℂ)/2)^(n+1))*(G n:ℂ) := by
    push_cast
    linear_combination 2*(2*(Real.pi:ℂ))^n*h
  rw [hratio,hneg,hcross] at hh
  linear_combination hh


/-- The manuscript's odd-index two-scale formula. -/
theorem oddScale : Contracts.oddScale := by
  intro n hn hodd
  have h := two_scale_complex n hn
  rw [hodd.neg_one_pow] at h
  have h4 : (4:ℂ)^n = (((4:ℝ)^n:ℝ):ℂ) := by norm_cast
  rw [h4] at h
  have hr := congrArg Complex.re h
  simp [← Complex.ofReal_pow,Complex.mul_re] at hr
  push_cast
  linear_combination hr

/-- Equation (2), retained undivided at the positive even specialization. -/
theorem evenScale : Contracts.evenScale := by
  intro m hm
  have h := two_scale_complex (2*m) (by omega)
  have hi : 2*(2*m)+1 = 4*m+1 := by omega
  have hsign : (-1:ℂ)^(2*m) = 1 := by rw [pow_mul]; norm_num
  have hp : (4:ℂ)^(2*m) = (16:ℂ)^m := by rw [pow_mul]; norm_num
  rw [hi,hsign,hp] at h
  have h16 : (16:ℂ)^m = (((16:ℝ)^m:ℝ):ℂ) := by norm_cast
  rw [h16] at h
  have hr := congrArg Complex.re h
  simp [← Complex.ofReal_pow,Complex.mul_re] at hr
  push_cast
  linear_combination hr

/-- Guarded odd reindexing and elimination without division by D. -/
theorem oddData : Contracts.oddData := by
  intro m hm
  have hn : 1 ≤ 2*m-1 := by omega
  have hodd : Odd (2*m-1) := by refine ⟨m-1,?_⟩; omega
  have hi : 2*(2*m-1)+1 = 4*m-1 := by omega
  have hC := oddCenter (2*m-1) hn hodd
  have hS := oddScale (2*m-1) hn hodd
  rw [hi] at hC hS
  have hD := (Elementary.oddCoefficients m hm).2.2
  constructor
  · linear_combination hC
  · linear_combination (((4:ℝ)^(2*m-1)+1)/2)*hC-(1/2:ℝ)*hS+
      (Real.pi^(4*m-1)/2)*hD

#print axioms ramanujanReal
#print axioms center
#print axioms oddCenter
#print axioms oddScale
#print axioms evenScale
#print axioms oddData

end Plouffe.Proofs.Specializations
