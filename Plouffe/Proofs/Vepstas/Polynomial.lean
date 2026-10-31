/-
Copyright (c) 2026 Patrick Lopatto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Lopatto
-/
module

public import Plouffe.Proofs.Vepstas.Parameters

public section
namespace Plouffe.Proofs.Vepstas

/-- The rational Bernoulli/factorial factor of a Vepstas summand, without its alternating sign. -/
noncomputable abbrev coeff (m k : ℕ) : ℚ :=
  bernoulli (2*k)*bernoulli (4*m+2-2*k)/
    ((Nat.factorial (2*k):ℚ)*(Nat.factorial (4*m+2-2*k):ℚ))

private theorem unit_four : (1+Complex.I)^4 = (-4:ℂ) := by
  have h : (1+Complex.I)^2 = 2*Complex.I := by ring_nf; norm_num
  rw [show (4:ℕ)=2*2 by omega,pow_mul,h]
  norm_num [mul_pow,Complex.I_sq]

private theorem factor_powers (a b : ℂ) (u v k : ℕ) (ha : a ≠ 0) (hk : k ≤ v) :
    a^u*a^(v-k)*b^k = a^(u+v)*(b/a)^k := by
  have he : a^(u+v) = a^u*a^(v-k)*a^k := by
    rw [← pow_add,← pow_add]
    congr 1
    omega
  rw [he,div_pow]
  field_simp

private theorem even_scalar (r : ℝ) :
    ((1+Complex.I)*(r:ℂ)).re-((1+Complex.I)*(r:ℂ)).im = 0 := by
  norm_num [Complex.mul_re,Complex.mul_im]

private theorem odd_scalar (r : ℝ) :
    ((1+Complex.I)*((r:ℂ)*(Complex.I/2))).re-
      ((1+Complex.I)*((r:ℂ)*(Complex.I/2))).im = -r := by
  norm_num [Complex.mul_re,Complex.mul_im]
  ring

private theorem real_mul_re_sub_im (r : ℝ) (z : ℂ) :
    ((r:ℂ)*z).re-((r:ℂ)*z).im = r*(z.re-z.im) := by
  simp only [Complex.mul_re,Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im]
  ring

/-- Isolate the real global factor and the elementary Gaussian phase of each term. -/
theorem polynomial_phase (m : ℕ) :
    transformed m = ((16:ℂ)^m*(-4:ℂ)^m*(Real.pi:ℂ)^(4*m+1))*
      ∑ k ∈ Finset.range (2*m+2), (coeff m k:ℂ)*((1+Complex.I)*(Complex.I/2)^k) := by
  have hp : (Real.pi:ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hu : (1:ℂ)+Complex.I ≠ 0 := by
    intro h
    have hh := congrArg Complex.re h
    norm_num at hh
  have hα : alpha ≠ 0 := mul_ne_zero hp hu
  have hr : beta/alpha = -Complex.I/2 := by
    dsimp [alpha,beta]
    field_simp [hu]
    ring_nf
    norm_num
    ring
  have hr' : (-1:ℂ)*(beta/alpha) = Complex.I/2 := by rw [hr]; ring
  have hunit : (1+Complex.I)^(4*m+1) = (-4:ℂ)^m*(1+Complex.I) := by
    rw [pow_add,pow_mul,unit_four,pow_one]
  have hA : alpha^(4*m+1) = (Real.pi:ℂ)^(4*m+1)*(-4:ℂ)^m*(1+Complex.I) := by
    dsimp [alpha]
    rw [mul_pow,hunit]
    ring
  dsimp [transformed,polynomial]
  rw [Finset.mul_sum,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  have hk' : k ≤ 2*m+1 := by have := Finset.mem_range.mp hk; omega
  have hf : alpha^(2*m)*alpha^(2*m+1-k)*beta^k = alpha^(4*m+1)*(beta/alpha)^k := by
    simpa only [show 2*m+(2*m+1)=4*m+1 by omega] using
      factor_powers alpha beta (2*m) (2*m+1) k hα hk'
  have hc : (((-1:ℚ)^k*bernoulli (2*k)*bernoulli (4*m+2-2*k)/
      ((Nat.factorial (2*k):ℚ)*(Nat.factorial (4*m+2-2*k):ℚ))) : ℂ) =
      (-1:ℂ)^k*(coeff m k:ℂ) := by dsimp [coeff]; push_cast; ring
  rw [hc]
  calc
    _ = (16:ℂ)^m*(coeff m k:ℂ)*(alpha^(2*m)*alpha^(2*m+1-k)*beta^k)*(-1:ℂ)^k := by ring
    _ = (16:ℂ)^m*(coeff m k:ℂ)*alpha^(4*m+1)*(((-1:ℂ)*(beta/alpha))^k) := by rw [hf]; simp only [mul_pow]; ring
    _ = _ := by rw [hr',hA]; ring

private theorem phase_even (j : ℕ) :
    (((1+Complex.I)*(Complex.I/2)^(2*j)).re-((1+Complex.I)*(Complex.I/2)^(2*j)).im) = 0 := by
  have h : (Complex.I/2)^2 = ((-1/4:ℝ):ℂ) := by norm_num [div_pow,Complex.I_sq]
  rw [pow_mul,h]
  have hp : (((-1/4:ℝ):ℂ))^j = (((-1/4:ℝ)^j:ℝ):ℂ) := by norm_cast
  rw [hp]
  exact even_scalar ((-1/4:ℝ)^j)

private theorem phase_odd (j : ℕ) :
    (((1+Complex.I)*(Complex.I/2)^(2*j+1)).re-((1+Complex.I)*(Complex.I/2)^(2*j+1)).im) =
      -(-1/4:ℝ)^j := by
  have h : (Complex.I/2)^2 = ((-1/4:ℝ):ℂ) := by norm_num [div_pow,Complex.I_sq]
  rw [pow_add,pow_mul,h,pow_one]
  have hp : (((-1/4:ℝ):ℂ))^j = (((-1/4:ℝ)^j:ℝ):ℂ) := by norm_cast
  rw [hp]
  exact odd_scalar ((-1/4:ℝ)^j)

private theorem pair_sum (f : ℕ → ℝ) (n : ℕ) :
    (∑ k ∈ Finset.range (2*n), f k) = ∑ j ∈ Finset.range n, (f (2*j)+f (2*j+1)) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [show 2*(n+1)=(2*n+1)+1 by omega,Finset.sum_range_succ,
      Finset.sum_range_succ,Finset.sum_range_succ,ih]
    ring

/-- The Re−Im functional kills the even coefficients and selects the odd coefficients. -/
theorem phase_sum (m : ℕ) :
    (∑ k ∈ Finset.range (2*m+2), (coeff m k:ℂ)*((1+Complex.I)*(Complex.I/2)^k)).re-
      (∑ k ∈ Finset.range (2*m+2), (coeff m k:ℂ)*((1+Complex.I)*(Complex.I/2)^k)).im =
      -(∑ j ∈ Finset.range (m+1), (-1/4:ℝ)^j*(coeff m (2*j+1):ℝ)) := by
  rw [Complex.re_sum,Complex.im_sum,← Finset.sum_sub_distrib]
  have ht (k : ℕ) : ((coeff m k:ℂ)*((1+Complex.I)*(Complex.I/2)^k)).re-
      ((coeff m k:ℂ)*((1+Complex.I)*(Complex.I/2)^k)).im =
      (coeff m k:ℝ)*(((1+Complex.I)*(Complex.I/2)^k).re-((1+Complex.I)*(Complex.I/2)^k).im) := by
    have hc : (coeff m k:ℂ) = ((coeff m k:ℝ):ℂ) := by norm_cast
    rw [hc]
    exact real_mul_re_sub_im _ _
  simp_rw [ht]
  rw [show 2*m+2=2*(m+1) by omega,pair_sum]
  simp_rw [phase_even,phase_odd,mul_zero,zero_add]
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro j hj
  ring


private theorem weighted_H (m : ℕ) :
    ((16:ℝ)^m*(-4:ℝ)^m)*(∑ j ∈ Finset.range (m+1), (-1/4:ℝ)^j*(coeff m (2*j+1):ℝ)) =
      (-4:ℝ)^m*(H m:ℝ) := by
  have href := Finset.sum_range_reflect (fun j => (-1/4:ℝ)^j*(coeff m (2*j+1):ℝ)) (m+1)
  simp only [Nat.add_sub_cancel] at href
  rw [← href]
  unfold H
  push_cast
  rw [Finset.mul_sum,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  have hk' : k ≤ m := by have := Finset.mem_range.mp hk; omega
  have hc : coeff m (2*(m-k)+1) =
      bernoulli (4*k)*bernoulli (4*m+2-4*k)/
        ((Nat.factorial (4*k):ℚ)*(Nat.factorial (4*m+2-4*k):ℚ)) := by
    dsimp [coeff]
    rw [show 2*(2*(m-k)+1)=4*m+2-4*k by omega,
      show 4*m+2-(4*m+2-4*k)=4*k by omega]
    ring
  have hpow : (-4:ℝ)^m*(-1/4:ℝ)^(m-k) = (-4:ℝ)^k := by
    have he : (-4:ℝ)^m = (-4:ℝ)^(m-k)*(-4:ℝ)^k := by rw [← pow_add,Nat.sub_add_cancel hk']
    rw [show (-1/4:ℝ)=(-4:ℝ)⁻¹ by norm_num,inv_pow,he]
    field_simp
  have h16 : (-4:ℝ)^m*(-4:ℝ)^m = (16:ℝ)^m := by rw [← mul_pow]; norm_num
  have hscalar : (16:ℝ)^m*(-4:ℝ)^m*(-1/4:ℝ)^(m-k) = (-4:ℝ)^m*((-4:ℝ)^m*(-4:ℝ)^k) := by
    calc
      _ = (16:ℝ)^m*(-4:ℝ)^k := by linear_combination (16:ℝ)^m*hpow
      _ = _ := by rw [← h16]; ring
  have hcr := congrArg (fun q : ℚ => (q:ℝ)) hc
  push_cast at hcr
  rw [hcr,pow_add]
  linear_combination ((bernoulli (4*k):ℝ)*(bernoulli (4*m+2-4*k):ℝ)/
    ((Nat.factorial (4*k):ℝ)*(Nat.factorial (4*m+2-4*k):ℝ)))*hscalar

/-- The Vepstas Bernoulli adapter; realness comes from the already proved transformation. -/
theorem vepstasPolynomial : Contracts.vepstasPolynomial := by
  intro m hm
  let g : ℝ := (16:ℝ)^m*(-4:ℝ)^m*Real.pi^(4*m+1)
  have hg : (16:ℂ)^m*(-4:ℂ)^m*(Real.pi:ℂ)^(4*m+1) = (g:ℂ) := by
    dsimp [g]
    push_cast
    ring
  have hf : (transformed m).re-(transformed m).im =
      -(-4:ℝ)^m*Real.pi^(4*m+1)*(H m:ℝ) := by
    rw [polynomial_phase m,hg,real_mul_re_sub_im,phase_sum]
    have hH := weighted_H m
    dsimp [g]
    linear_combination -(Real.pi^(4*m+1))*hH
  have hi := transformed_im_zero m hm
  have he : transformed m = ((-(-4:ℝ)^m*Real.pi^(4*m+1)*(H m:ℝ):ℝ):ℂ) := by
    apply Complex.ext
    · simp only [Complex.ofReal_re]
      linarith
    · simpa only [Complex.ofReal_im] using hi
  change transformed m = _
  convert he using 1; push_cast; ring

#print axioms vepstasPolynomial

end Plouffe.Proofs.Vepstas
