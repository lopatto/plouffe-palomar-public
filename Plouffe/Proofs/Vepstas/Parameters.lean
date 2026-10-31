/-
Copyright (c) 2026 Patrick Lopatto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Lopatto
-/
module

public import Plouffe.Proofs.Ramanujan
public import Plouffe.Proofs.Parity
public import Plouffe.Proofs.Specializations

public section
namespace Plouffe.Proofs.Vepstas

/-- The complex parameter `π*(1+i)` used in the Vepstas specialization. -/
noncomputable abbrev alpha : ℂ := (Real.pi:ℂ)*(1+Complex.I)
/-- The paired complex parameter `π*(1-i)/2` used in the Vepstas specialization. -/
noncomputable abbrev beta : ℂ := (Real.pi:ℂ)*(1-Complex.I)/2
/-- The finite complex Bernoulli sum at the Vepstas parameters `alpha` and `beta`. -/
noncomputable abbrev polynomial (m : ℕ) : ℂ :=
  ∑ k ∈ Finset.range (2*m+2), ((-1:ℚ)^k*bernoulli (2*k)*bernoulli (4*m+2-2*k)/
    ((Nat.factorial (2*k):ℚ)*(Nat.factorial (4*m+2-2*k):ℚ)):ℂ)*alpha^(2*m+1-k)*beta^k
/-- The Bernoulli sum `polynomial m` multiplied by `16^m*alpha^(2*m)`. -/
noncomputable abbrev transformed (m : ℕ) : ℂ := (16:ℂ)^m*alpha^(2*m)*polynomial m

private theorem alpha_re_pos : 0 < alpha.re := by simpa [alpha] using Real.pi_pos
private theorem beta_re_pos : 0 < beta.re := by
  norm_num [beta,Complex.mul_re,Complex.div_re]
  positivity
private theorem alpha_ne_zero : alpha ≠ 0 := by intro h; have := alpha_re_pos; simp [h] at this
private theorem beta_ne_zero : beta ≠ 0 := by intro h; have := beta_re_pos; simp [h] at this
private theorem parameter_product : alpha*beta = (Real.pi:ℂ)^2 := by
  dsimp [alpha,beta]
  ring_nf
  norm_num
  ring

private theorem parameter_ratio (m : ℕ) :
    alpha^(2*m)*(beta^(2*m))⁻¹ = (-4:ℂ)^m := by
  have hr : alpha/beta = 2*Complex.I := by
    dsimp [alpha,beta]
    have hp : (Real.pi:ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
    have hi : (1:ℂ)-Complex.I ≠ 0 := by
      intro h
      have hh := congrArg Complex.re h
      norm_num at hh
    field_simp [hi]
    ring_nf
    norm_num
    ring
  rw [← div_eq_mul_inv,← div_pow,hr,pow_mul]
  norm_num [mul_pow,Complex.I_sq]

/-- The scaled Bernoulli polynomial is real by Ramanujan and convergent Lambert parity. -/
theorem transformed_eq (m : ℕ) (hm : 1 ≤ m) :
    transformed m = (-4:ℂ)^m*(riemannZeta ((4*m+1:ℕ):ℂ)/2+
      ((S (4*m+1) 2+T (4*m+1) 2:ℝ):ℂ)/(2:ℂ)^(4*m+1)-(T (4*m+1) 1:ℂ))-
      (riemannZeta ((4*m+1:ℕ):ℂ)/2+(S (4*m+1) 2:ℂ)) := by
  have h := Ramanujan.ramanujanComplex (2*m) alpha beta (by omega)
    alpha_re_pos beta_re_pos parameter_product
  have hi : 2*(2*m)+1 = 4*m+1 := by omega
  have hi2 : 2*(2*m)+2 = 4*m+2 := by omega
  have h4 : (4:ℂ)^(2*m) = (16:ℂ)^m := by rw [pow_mul]; norm_num
  have hn : (-beta)^(2*m) = beta^(2*m) := by
    rw [show -beta = (-1:ℂ)*beta by ring,mul_pow,pow_mul]
    norm_num
  rw [hi,hi2,h4,hn] at h
  have hPar := Parity.lambertParity (2*m)
  rw [hi] at hPar
  rw [hPar.1,hPar.2] at h
  have h' : (alpha^(2*m))⁻¹*(riemannZeta ((4*m+1:ℕ):ℂ)/2+(S (4*m+1) 2:ℂ)) =
    (beta^(2*m))⁻¹*(riemannZeta ((4*m+1:ℕ):ℂ)/2+
      ((S (4*m+1) 2+T (4*m+1) 2:ℝ):ℂ)/(2:ℂ)^(4*m+1)-(T (4*m+1) 1:ℂ))-
    (16:ℂ)^m*polynomial m := by
      dsimp [polynomial]
      push_cast at h ⊢
      linear_combination h
  have hc : alpha^(2*m)*(alpha^(2*m))⁻¹ = 1 := mul_inv_cancel₀ (pow_ne_zero _ alpha_ne_zero)
  have hh : (alpha^(2*m)*(alpha^(2*m))⁻¹)*
      (riemannZeta ((4*m+1:ℕ):ℂ)/2+(S (4*m+1) 2:ℂ)) =
    (alpha^(2*m)*(beta^(2*m))⁻¹)*
      (riemannZeta ((4*m+1:ℕ):ℂ)/2+
        ((S (4*m+1) 2+T (4*m+1) 2:ℝ):ℂ)/(2:ℂ)^(4*m+1)-(T (4*m+1) 1:ℂ))-
    transformed m := by dsimp [transformed]; linear_combination alpha^(2*m)*h'
  rw [hc,parameter_ratio] at hh
  linear_combination hh

theorem transformed_im_zero (m : ℕ) (hm : 1 ≤ m) : (transformed m).im = 0 := by
  have hr : transformed m = (((-4:ℝ)^m*((riemannZeta ((4*m+1:ℕ):ℂ)).re/2+
      (S (4*m+1) 2+T (4*m+1) 2)/(2:ℝ)^(4*m+1)-T (4*m+1) 1)-
      ((riemannZeta ((4*m+1:ℕ):ℂ)).re/2+S (4*m+1) 2):ℝ):ℂ) := by
    rw [transformed_eq m hm,Zeta.zetaReal (4*m+1) (by omega)]
    push_cast
    rfl
  rw [hr]
  rfl

end Plouffe.Proofs.Vepstas
