/-
Copyright (c) 2026 Patrick Lopatto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Lopatto
-/
module

public import Plouffe.Proofs.Vepstas.Polynomial

public section
namespace Plouffe.Proofs.Vepstas

private theorem vepstas_scalar (p q P z X Y W U V h g : ℝ)
    (hq : q ≠ 0) (hp : p = q^2)
    (hc : -q*P*h = q*(z/2+(Y+V)/(2*p)-U)-(z/2+Y))
    (hz : z*(p-1) = -2*p*X+2*W-p*P*g)
    (hT1 : U = X-2*Y) (hT2 : V = Y-2*W) :
    (1+q-2*p)*z = 2*V+2*(2*p-q)*Y+2*p*P*h+p*P*g := by
  have hp0 : p ≠ 0 := by rw [hp]; exact pow_ne_zero _ hq
  have hclear : -2*p*q*P*h = p*q*z+q*(Y+V)-2*p*q*U-p*z-2*p*Y := by
    have hh := hc
    field_simp at hh
    linear_combination hh
  apply mul_left_cancel₀ hq
  linear_combination hclear-q*hz-2*p*q*hT1-q*hT2-(z+2*Y)*hp

/-- The Vepstas identity follows from the proved complex transformation and polynomial adapter. -/
theorem vepstas : Contracts.vepstas := by
  intro m hm
  have hc : -(-4:ℝ)^m*Real.pi^(4*m+1)*(H m:ℝ) =
      (-4:ℝ)^m*((riemannZeta ((4*m+1:ℕ):ℂ)).re/2+
        (S (4*m+1) 2+T (4*m+1) 2)/(2:ℝ)^(4*m+1)-T (4*m+1) 1)-
      ((riemannZeta ((4*m+1:ℕ):ℂ)).re/2+S (4*m+1) 2) := by
    apply Complex.ofReal_injective
    push_cast
    have hZ := Zeta.zetaReal (4*m+1) (by omega)
    push_cast at hZ
    rw [← hZ]
    have he := transformed_eq m hm
    have hp := vepstasPolynomial m hm
    change transformed m = -(-4:ℂ)^m*(Real.pi:ℂ)^(4*m+1)*(H m:ℂ) at hp
    rw [hp] at he
    push_cast at he
    linear_combination he
  have hz := Specializations.evenScale m hm
  have ht1 := Series.fermiBose (4*m+1) 1 (by norm_num)
  have ht2 := Series.fermiBose (4*m+1) 2 (by norm_num)
  norm_num only [mul_one,show (2:ℝ)*2=4 by norm_num] at ht1 ht2
  obtain ⟨_,_,_,hA,_,_,_,_⟩ := Elementary.kCoefficients m hm
  rw [hA] at hc
  have hq : (-4:ℝ)^m ≠ 0 := pow_ne_zero _ (by norm_num)
  have hp : (16:ℝ)^m = ((-4:ℝ)^m)^2 := by rw [← pow_mul,mul_comm m 2,pow_mul]; norm_num
  have h := vepstas_scalar ((16:ℝ)^m) ((-4:ℝ)^m) (Real.pi^(4*m+1))
    ((riemannZeta ((4*m+1:ℕ):ℂ)).re) (S (4*m+1) 1) (S (4*m+1) 2) (S (4*m+1) 4)
    (T (4*m+1) 1) (T (4*m+1) 2) (H m:ℝ) (G (2*m):ℝ) hq hp hc hz ht1 ht2
  have hp0 : (2:ℝ)^(4*m) = (16:ℝ)^m := by rw [pow_mul]; norm_num
  rw [hA,hp0]
  exact h

private theorem even_data_scalar (p q k e P z X Y W V h g : ℝ)
    (hk : 2*k*(1+q-2*p) = 1-p)
    (he : e = p/2*g-2*p*k*h-p*k*g)
    (hz : z*(p-1) = -2*p*X+2*W-p*P*g)
    (hv : (1+q-2*p)*z = 2*V+2*(2*p-q)*Y+2*p*P*h+p*P*g)
    (ht : V = Y-2*W) :
    e*P = -p*X+2*k*(2*p-q+1)*Y+(1-4*k)*W := by
  linear_combination (1/2:ℝ)*hz+k*hv-(z/2)*hk+P*he+2*k*ht

/-- The even-family identity is obtained by undivided elimination, without using E nonzero. -/
theorem evenData : Contracts.evenData := by
  intro m hm
  obtain ⟨hden,_,hp4,hp2,_,_,_,_⟩ := Elementary.kCoefficients m hm
  have hK : 2*K m*(1+(-4:ℚ)^m-(2:ℚ)^(4*m+1)) = 1-(4:ℚ)^(2*m) := by
    unfold K
    field_simp [hden]
  have hKr : 2*(K m:ℝ)*(1+(-4:ℝ)^m-(2:ℝ)^(4*m+1)) = 1-(4:ℝ)^(2*m) := by exact_mod_cast hK
  rw [hp4,hp2] at hKr
  have hp0 : (2:ℝ)^(4*m) = (16:ℝ)^m := by rw [pow_mul]; norm_num
  have he : (E m:ℝ) = (16:ℝ)^m/2*(G (2*m):ℝ)-
      2*(16:ℝ)^m*(K m:ℝ)*(H m:ℝ)-(16:ℝ)^m*(K m:ℝ)*(G (2*m):ℝ) := by
    unfold E
    push_cast
    rw [hp4,hp2,hp0]
  have hv := vepstas m hm
  rw [hp2,hp0] at hv
  have ht := Series.fermiBose (4*m+1) 2 (by norm_num)
  norm_num only [show (2:ℝ)*2=4 by norm_num] at ht
  have h := even_data_scalar ((16:ℝ)^m) ((-4:ℝ)^m) (K m:ℝ) (E m:ℝ)
    (Real.pi^(4*m+1)) ((riemannZeta ((4*m+1:ℕ):ℂ)).re)
    (S (4*m+1) 1) (S (4*m+1) 2) (S (4*m+1) 4) (T (4*m+1) 2)
    (H m:ℝ) (G (2*m):ℝ) hKr he (Specializations.evenScale m hm) hv ht
  simpa only [hp4,hp2] using h

#print axioms vepstas
#print axioms evenData

end Plouffe.Proofs.Vepstas
