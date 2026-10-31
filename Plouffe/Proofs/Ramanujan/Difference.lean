/-
Copyright (c) 2026 Patrick Lopatto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Lopatto
-/
module

public import Plouffe.Proofs.Ramanujan.DoubleSeries

public section
namespace Plouffe.Proofs.Ramanujan

private noncomputable abbrev dTerm (n : ℕ) (a b : ℂ) (kl : ℕ × ℕ) : ℂ :=
  1 / (((kl.1+1:ℕ):ℂ)^(2*n)*(a*((kl.1+1:ℕ):ℂ)^2+b*((kl.2+1:ℕ):ℂ)^2))

private noncomputable abbrev pTerm (n : ℕ) (a b : ℂ) (j : ℕ) (kl : ℕ × ℕ) : ℂ :=
  ((-1:ℂ)^j*(a^(n-j))⁻¹*(b^(j+1))⁻¹)*
    ((1/((kl.1+1:ℕ):ℂ)^(2*(n-j)))*(1/((kl.2+1:ℕ):ℂ)^(2*(j+1))))

private theorem norm_dirichlet_summable (r : ℕ) (hr : 2 ≤ r) :
    Summable (fun k : ℕ => ‖1/((k+1:ℕ):ℂ)^r‖) := by
  have h : Summable (fun k : ℕ => 1/((k+1:ℕ):ℝ)^r) :=
    (summable_nat_add_iff 1).mpr (Real.summable_one_div_nat_pow.mpr (by omega))
  simpa only [norm_div, norm_one, norm_pow, Complex.norm_natCast] using h

private theorem pTerm_summable (n : ℕ) (a b : ℂ) (j : ℕ) (hj : j < n) :
    Summable (pTerm n a b j) := by
  exact (summable_mul_of_summable_norm (norm_dirichlet_summable _ (by omega))
    (norm_dirichlet_summable _ (by omega))).mul_left _

private theorem pTerm_tsum (n : ℕ) (a b : ℂ) (j : ℕ) (hj : j < n) :
    ∑' kl : ℕ × ℕ, pTerm n a b j kl =
      ((-1:ℂ)^j*(a^(n-j))⁻¹*(b^(j+1))⁻¹)*
        riemannZeta ((2*(n-j):ℕ):ℂ)*riemannZeta ((2*(j+1):ℕ):ℂ) := by
  have h₁ := norm_dirichlet_summable (2*(n-j)) (by omega)
  have h₂ := norm_dirichlet_summable (2*(j+1)) (by omega)
  have hprod := summable_mul_of_summable_norm h₁ h₂
  rw [show (fun kl : ℕ × ℕ => pTerm n a b j kl) =
    (fun kl : ℕ × ℕ => ((-1:ℂ)^j*(a^(n-j))⁻¹*(b^(j+1))⁻¹)*
      ((1/((kl.1+1:ℕ):ℂ)^(2*(n-j)))*(1/((kl.2+1:ℕ):ℂ)^(2*(j+1))))) from rfl,
    hprod.tsum_mul_left, ← tsum_mul_tsum_of_summable_norm h₁ h₂,
    ← (Zeta.zetaPositiveSeries (2*(n-j)) (by omega)).2,
    ← (Zeta.zetaPositiveSeries (2*(j+1)) (by omega)).2]
  ring

/-- The absolutely convergent difference of double kernels separates into even zeta values. -/
theorem double_difference (n : ℕ) (a b : ℂ) (hn : 1 ≤ n)
    (ha : 0 < a.re) (hb : 0 < b.re) :
    (a^n)⁻¹*(∑' kl : ℕ × ℕ, 1 / (((kl.1+1:ℕ):ℂ)^(2*n)*
      (a*((kl.1+1:ℕ):ℂ)^2+b*((kl.2+1:ℕ):ℂ)^2)))-
    (-1:ℂ)^n*(b^n)⁻¹*(∑' kl : ℕ × ℕ, 1 / (((kl.1+1:ℕ):ℂ)^(2*n)*
      (b*((kl.1+1:ℕ):ℂ)^2+a*((kl.2+1:ℕ):ℂ)^2))) =
    ∑ j ∈ Finset.range n, ((-1:ℂ)^j*(a^(n-j))⁻¹*(b^(j+1))⁻¹)*
      riemannZeta ((2*(n-j):ℕ):ℂ)*riemannZeta ((2*(j+1):ℕ):ℂ) := by
  have ha0 : a ≠ 0 := by intro h; simp [h] at ha
  have hb0 : b ≠ 0 := by intro h; simp [h] at hb
  have hDa := Double.doubleSummable n a b hn ha hb
  have hDb := Double.doubleSummable n b a hn hb ha
  have hDa' : Summable (dTerm n a b) := hDa
  have hDb' : Summable (fun kl : ℕ × ℕ => dTerm n b a (kl.2,kl.1)) := by
    simpa only [dTerm, Prod.swap] using hDb.prod_symm
  have hswap : (∑' kl : ℕ × ℕ, dTerm n b a kl) =
      ∑' kl : ℕ × ℕ, dTerm n b a (kl.2,kl.1) := by
    exact (Equiv.prodComm ℕ ℕ).tsum_eq _ |>.symm
  have hpoint (kl : ℕ × ℕ) : (a^n)⁻¹*dTerm n a b kl-
      ((-1:ℂ)^n*(b^n)⁻¹)*dTerm n b a (kl.2,kl.1) =
      ∑ j ∈ Finset.range n, pTerm n a b j kl := by
    have hk : ((kl.1+1:ℕ):ℂ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero kl.1
    have hl : ((kl.2+1:ℕ):ℂ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero kl.2
    have hd : a*((kl.1+1:ℕ):ℂ)^2+b*((kl.2+1:ℕ):ℂ)^2 ≠ 0 := by
      intro h
      have hre : 0 < (a*((kl.1+1:ℕ):ℂ)^2+b*((kl.2+1:ℕ):ℂ)^2).re := by
        have he : (a*((kl.1+1:ℕ):ℂ)^2+b*((kl.2+1:ℕ):ℂ)^2).re =
            a.re*((kl.1+1:ℕ):ℝ)^2+b.re*((kl.2+1:ℕ):ℝ)^2 := by simp [Complex.mul_re,pow_two]
        rw [he]
        exact add_pos (mul_pos ha (pow_pos (by positivity) _)) (mul_pos hb (pow_pos (by positivity) _))
      rw [h] at hre
      exact (lt_irrefl 0) hre
    have hf := Elementary.finitePartialFractions n (a*((kl.1+1:ℕ):ℂ)^2)
      (b*((kl.2+1:ℕ):ℂ)^2) hn (mul_ne_zero ha0 (pow_ne_zero _ hk))
      (mul_ne_zero hb0 (pow_ne_zero _ hl)) hd
    have he : (a^n)⁻¹*dTerm n a b kl-
        ((-1:ℂ)^n*(b^n)⁻¹)*dTerm n b a (kl.2,kl.1) =
      (((a*((kl.1+1:ℕ):ℂ)^2)^n)⁻¹-(-1:ℂ)^n*((b*((kl.2+1:ℕ):ℂ)^2)^n)⁻¹)/
        (a*((kl.1+1:ℕ):ℂ)^2+b*((kl.2+1:ℕ):ℂ)^2) := by
      simp only [dTerm, mul_pow, ← pow_mul, one_div, mul_inv_rev]
      ring
    rw [he,hf]
    apply Finset.sum_congr rfl
    intro j hj
    simp only [pTerm, mul_pow, ← pow_mul, one_div, mul_inv_rev]
    ring
  change (a^n)⁻¹*(∑' kl : ℕ × ℕ, dTerm n a b kl)-
    ((-1:ℂ)^n*(b^n)⁻¹)*(∑' kl : ℕ × ℕ, dTerm n b a kl) = _
  rw [hswap, ← hDa'.tsum_mul_left ((a^n)⁻¹), ← hDb'.tsum_mul_left ((-1:ℂ)^n*(b^n)⁻¹),
    ← (hDa'.mul_left _).tsum_sub (hDb'.mul_left _), tsum_congr hpoint,
    Summable.tsum_finsetSum (fun j hj => pTerm_summable n a b j (Finset.mem_range.mp hj))]
  apply Finset.sum_congr rfl
  intro j hj
  exact pTerm_tsum n a b j (Finset.mem_range.mp hj)

end Plouffe.Proofs.Ramanujan
