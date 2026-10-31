/-
Copyright (c) 2026 Patrick Lopatto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Lopatto
-/
module

public import Plouffe.Proofs.Ramanujan.Difference

public section
namespace Plouffe.Proofs.Ramanujan

/-- Euler's even-zeta formula normalized for a pair of modular parameters. -/
theorem even_zeta_normalized (r : ℕ) (hr : 1 ≤ r) (a b : ℂ)
    (hab : a*b = (Real.pi:ℂ)^2) :
    riemannZeta ((2*r:ℕ):ℂ) =
      ((-1:ℂ)^(r+1)*(4:ℂ)^r*(a*b)^r*(bernoulli (2*r):ℂ))/
        (2*(Nat.factorial (2*r):ℂ)) := by
  have htwo : (2:ℂ)^(2*r-1) = (4:ℂ)^r/2 := by
    apply (eq_div_iff (by norm_num : (2:ℂ) ≠ 0)).2
    calc
      (2:ℂ)^(2*r-1)*2 = (2:ℂ)^((2*r-1)+1) := by rw [pow_succ]
      _ = (2:ℂ)^(2*r) := by congr 1; omega
      _ = (4:ℂ)^r := by rw [pow_mul]; norm_num
  have hp : (Real.pi:ℂ)^(2*r) = (a*b)^r := by rw [pow_mul,hab]
  have hz := riemannZeta_two_mul_nat (k := r) (by omega)
  push_cast
  rw [hz,htwo,hp]
  simp only [div_eq_mul_inv, mul_inv_rev]
  ring


/-- Each interior Euler product is the corresponding Bernoulli-convolution term. -/
theorem even_zeta_product (n j : ℕ) (a b : ℂ) (hj : j < n)
    (ha : a ≠ 0) (hb : b ≠ 0) (hab : a*b = (Real.pi:ℂ)^2) :
    ((-1:ℂ)^j*(a^(n-j))⁻¹*(b^(j+1))⁻¹)*
      riemannZeta ((2*(n-j):ℕ):ℂ)*riemannZeta ((2*(j+1):ℕ):ℂ) =
    -(4:ℂ)^n * (((-1:ℚ)^(n-j)*bernoulli (2*(n-j))*bernoulli (2*(j+1))/
      ((Nat.factorial (2*(n-j)):ℚ)*(Nat.factorial (2*(j+1)):ℚ)) : ℚ):ℂ)*
      a^(j+1)*b^(n-j) := by
  let r := n-j
  let t := j+1
  have hrt : r+t = n+1 := by dsimp [r,t]; omega
  have hsgn : (-1:ℂ)^j*(-1:ℂ)^(r+1)*(-1:ℂ)^(t+1) = -(-1:ℂ)^r := by
    rw [← pow_add, ← pow_add]
    have he : j+(r+1)+(t+1) = r+1+2*(j+1) := by dsimp [t]; omega
    rw [he,pow_add,pow_mul]
    norm_num
    rw [pow_succ]
    ring
  have h4 : (4:ℂ)^r*(4:ℂ)^t = 4*(4:ℂ)^n := by rw [← pow_add,hrt,pow_succ]; ring
  have hp : (a^r)⁻¹*(b^t)⁻¹*(a*b)^r*(a*b)^t = a^t*b^r := by
    simp only [mul_pow]
    calc
      _ = ((a^r)⁻¹*a^r)*((b^t)⁻¹*b^t)*a^t*b^r := by ring
      _ = _ := by rw [inv_mul_cancel₀ (pow_ne_zero _ ha),inv_mul_cancel₀ (pow_ne_zero _ hb)]; ring
  rw [even_zeta_normalized (n-j) (by omega) a b hab,
    even_zeta_normalized (j+1) (by omega) a b hab]
  push_cast
  change ((-1:ℂ)^j*(a^r)⁻¹*(b^t)⁻¹)*
    (((-1:ℂ)^(r+1)*(4:ℂ)^r*(a*b)^r*(bernoulli (2*r):ℂ))/(2*(Nat.factorial (2*r):ℂ)))*
    (((-1:ℂ)^(t+1)*(4:ℂ)^t*(a*b)^t*(bernoulli (2*t):ℂ))/(2*(Nat.factorial (2*t):ℂ))) =
    -(4:ℂ)^n*((-1:ℂ)^r*(bernoulli (2*r):ℂ)*(bernoulli (2*t):ℂ)/
      ((Nat.factorial (2*r):ℂ)*(Nat.factorial (2*t):ℂ)))*a^t*b^r
  calc
    _ = ((-1:ℂ)^j*(-1:ℂ)^(r+1)*(-1:ℂ)^(t+1))*((4:ℂ)^r*(4:ℂ)^t)*
      ((a^r)⁻¹*(b^t)⁻¹*(a*b)^r*(a*b)^t)*(bernoulli (2*r):ℂ)*(bernoulli (2*t):ℂ)/
      (4*((Nat.factorial (2*r):ℂ)*(Nat.factorial (2*t):ℂ))) := by
        simp only [div_eq_mul_inv,mul_inv_rev]
        ring
    _ = _ := by
      rw [hsgn,h4,hp]
      simp only [div_eq_mul_inv,mul_inv_rev]
      ring


private noncomputable abbrev convTerm (n : ℕ) (a b : ℂ) (k : ℕ) : ℂ :=
  (((-1:ℚ)^k*bernoulli (2*k)*bernoulli (2*n+2-2*k)/
    ((Nat.factorial (2*k):ℚ)*(Nat.factorial (2*n+2-2*k):ℚ))) : ℂ)*a^(n+1-k)*b^k

private theorem conv_zero (n : ℕ) (a b : ℂ) :
    convTerm n a b 0 = ((bernoulli (2*n+2):ℂ)/(Nat.factorial (2*n+2):ℂ))*a^(n+1) := by
  simp [convTerm]

private theorem conv_last (n : ℕ) (a b : ℂ) :
    convTerm n a b (n+1) = (-1:ℂ)^(n+1)*
      ((bernoulli (2*n+2):ℂ)/(Nat.factorial (2*n+2):ℂ))*b^(n+1) := by
  simp [convTerm,show 2*(n+1)=2*n+2 by omega]
  left
  ring

private theorem endpoint_power (n : ℕ) (a b : ℂ) (ha : a ≠ 0) :
    (a^n)⁻¹*(a*b)^(n+1)/a = b^(n+1) := by
  rw [mul_pow,pow_succ a]
  field_simp

private theorem bernoulli_endpoints (n : ℕ) (a b : ℂ) (ha : a ≠ 0) (hb : b ≠ 0)
    (hab : a*b = (Real.pi:ℂ)^2) :
    (a^n)⁻¹*(riemannZeta ((2*n+2:ℕ):ℂ)/(2*a))-
      (-1:ℂ)^n*(b^n)⁻¹*(riemannZeta ((2*n+2:ℕ):ℂ)/(2*b)) =
    -(4:ℂ)^n*(convTerm n a b 0+convTerm n a b (n+1)) := by
  have hz := even_zeta_normalized (n+1) (by omega) a b hab
  rw [show 2*(n+1)=2*n+2 by omega] at hz
  have h4 : (4:ℂ)^(n+1) = 4*(4:ℂ)^n := by rw [pow_succ]; ring
  have hsign : (-1:ℂ)^n*(-1:ℂ)^(n+2) = 1 := by
    rw [← pow_add,show n+(n+2)=2*(n+1) by omega,pow_mul]
    norm_num
  have hsign' : (-1:ℂ)^(n+2) = -(-1:ℂ)^(n+1) := by
    rw [show n+2=(n+1)+1 by omega,pow_succ]
    ring
  have hA : (a^n)⁻¹*(riemannZeta ((2*n+2:ℕ):ℂ)/(2*a)) = -(4:ℂ)^n*convTerm n a b (n+1) := by
    rw [hz,conv_last]
    change (a^n)⁻¹*(((-1:ℂ)^(n+2)*(4:ℂ)^(n+1)*(a*b)^(n+1)*(bernoulli (2*n+2):ℂ)/
      (2*(Nat.factorial (2*n+2):ℂ)))/(2*a)) = _
    calc
      _ = ((-1:ℂ)^(n+2))*(4:ℂ)^n*((a^n)⁻¹*(a*b)^(n+1)/a)*
        ((bernoulli (2*n+2):ℂ)/(Nat.factorial (2*n+2):ℂ)) := by
          rw [h4]
          simp only [div_eq_mul_inv,mul_inv_rev]
          ring
      _ = _ := by rw [endpoint_power n a b ha,hsign']; ring
  have hB : -(-1:ℂ)^n*(b^n)⁻¹*(riemannZeta ((2*n+2:ℕ):ℂ)/(2*b)) = -(4:ℂ)^n*convTerm n a b 0 := by
    rw [hz,conv_zero]
    change -(-1:ℂ)^n*(b^n)⁻¹*(((-1:ℂ)^(n+2)*(4:ℂ)^(n+1)*(a*b)^(n+1)*(bernoulli (2*n+2):ℂ)/
      (2*(Nat.factorial (2*n+2):ℂ)))/(2*b)) = _
    calc
      _ = -((-1:ℂ)^n*(-1:ℂ)^(n+2))*(4:ℂ)^n*((b^n)⁻¹*(b*a)^(n+1)/b)*
        ((bernoulli (2*n+2):ℂ)/(Nat.factorial (2*n+2):ℂ)) := by
          rw [h4]
          simp only [div_eq_mul_inv,mul_inv_rev]
          ring
      _ = _ := by rw [endpoint_power n b a hb,hsign]; ring
  linear_combination hA+hB


/-- Euler's separated zeta products, with both endpoint terms, are the full convolution. -/
theorem bernoulli_convolution (n : ℕ) (a b : ℂ) (ha : a ≠ 0) (hb : b ≠ 0)
    (hab : a*b = (Real.pi:ℂ)^2) :
    ((a^n)⁻¹*(riemannZeta ((2*n+2:ℕ):ℂ)/(2*a))-
      (-1:ℂ)^n*(b^n)⁻¹*(riemannZeta ((2*n+2:ℕ):ℂ)/(2*b)))+
      (∑ j ∈ Finset.range n, ((-1:ℂ)^j*(a^(n-j))⁻¹*(b^(j+1))⁻¹)*
        riemannZeta ((2*(n-j):ℕ):ℂ)*riemannZeta ((2*(j+1):ℕ):ℂ)) =
    -(4:ℂ)^n*∑ k ∈ Finset.range (n+2),
      (((-1:ℚ)^k*bernoulli (2*k)*bernoulli (2*n+2-2*k)/
        ((Nat.factorial (2*k):ℚ)*(Nat.factorial (2*n+2-2*k):ℚ))) : ℂ)*a^(n+1-k)*b^k := by
  have hinterior : (∑ j ∈ Finset.range n, ((-1:ℂ)^j*(a^(n-j))⁻¹*(b^(j+1))⁻¹)*
      riemannZeta ((2*(n-j):ℕ):ℂ)*riemannZeta ((2*(j+1):ℕ):ℂ)) =
      -(4:ℂ)^n*(∑ j ∈ Finset.range n, convTerm n a b (n-j)) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    have hjn : j < n := Finset.mem_range.mp hj
    have he : convTerm n a b (n-j) =
        (((-1:ℚ)^(n-j)*bernoulli (2*(n-j))*bernoulli (2*(j+1))/
          ((Nat.factorial (2*(n-j)):ℚ)*(Nat.factorial (2*(j+1)):ℚ))) : ℂ)*a^(j+1)*b^(n-j) := by
      dsimp [convTerm]
      rw [show 2*n+2-2*(n-j)=2*(j+1) by omega,show n+1-(n-j)=j+1 by omega]
    rw [he]
    have hp := even_zeta_product n j a b hjn ha hb hab
    push_cast at hp ⊢
    simpa only [mul_assoc] using hp
  have hreflect : (∑ j ∈ Finset.range n, convTerm n a b (n-j)) =
      ∑ j ∈ Finset.range n, convTerm n a b (j+1) := by
    calc
      _ = ∑ j ∈ Finset.range n, convTerm n a b ((n-1-j)+1) := by
        apply Finset.sum_congr rfl
        intro j hj
        congr 1
        have := Finset.mem_range.mp hj
        omega
      _ = _ := Finset.sum_range_reflect (fun j => convTerm n a b (j+1)) n
  have hfull : (∑ k ∈ Finset.range (n+2), convTerm n a b k) =
      convTerm n a b 0+(∑ j ∈ Finset.range n, convTerm n a b (n-j))+convTerm n a b (n+1) := by
    rw [Finset.sum_range_succ,Finset.sum_range_succ',← hreflect]
    ring
  change _ = -(4:ℂ)^n*∑ k ∈ Finset.range (n+2), convTerm n a b k
  rw [bernoulli_endpoints n a b ha hb hab,hinterior,hfull]
  ring

end Plouffe.Proofs.Ramanujan
