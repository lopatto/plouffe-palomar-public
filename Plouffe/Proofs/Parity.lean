/-
Copyright (c) 2026 Patrick Lopatto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Lopatto
-/
module

public import Plouffe.Proofs.Series
public import Plouffe.Contracts
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Topology.Algebra.InfiniteSum.NatInt

public section
namespace Plouffe.Proofs.Parity

private theorem exp_alpha (k : ℕ) :
    Complex.exp (2*((Real.pi:ℂ)*(1+Complex.I))*(k:ℂ)) =
      (Real.exp (2*Real.pi*(k:ℝ)):ℂ) := by
  rw [show 2*((Real.pi:ℂ)*(1+Complex.I))*(k:ℂ) =
    (2*(Real.pi:ℂ)*(k:ℂ))+(k:ℂ)*(2*(Real.pi:ℂ)*Complex.I) by ring,
    Complex.exp_add,Complex.exp_nat_mul_two_pi_mul_I,mul_one,Complex.ofReal_exp]
  congr 1
  push_cast
  ring

private theorem exp_beta (k : ℕ) :
    Complex.exp (2*((Real.pi:ℂ)*(1-Complex.I)/2)*(k:ℂ)) =
      (Real.exp (Real.pi*(k:ℝ)):ℂ)*(-1:ℂ)^k := by
  rw [show 2*((Real.pi:ℂ)*(1-Complex.I)/2)*(k:ℂ) =
    (Real.pi:ℂ)*(k:ℂ)+(k:ℂ)*(-((Real.pi:ℂ)*Complex.I)) by ring,
    Complex.exp_add,Complex.exp_nat_mul,Complex.exp_neg_pi_mul_I,Complex.ofReal_exp]
  congr 2
  push_cast
  rfl

private noncomputable def bose (s : ℕ) (r : ℝ) (j : ℕ) : ℂ :=
  ((1 / (((j+1:ℕ):ℝ)^s*(Real.exp (Real.pi*r*((j+1:ℕ):ℝ))-1)) : ℝ):ℂ)

private noncomputable def fermi (s : ℕ) (r : ℝ) (j : ℕ) : ℂ :=
  ((1 / (((j+1:ℕ):ℝ)^s*(Real.exp (Real.pi*r*((j+1:ℕ):ℝ))+1)) : ℝ):ℂ)

private noncomputable def lam (n : ℕ) (a : ℂ) (j : ℕ) : ℂ :=
  1 / (((j+1:ℕ):ℂ)^(2*n+1)*(Complex.exp (2*a*((j+1:ℕ):ℂ))-1))

private theorem lam_even (n j : ℕ) :
    lam n ((Real.pi:ℂ)*(1-Complex.I)/2) (2*j) = -fermi (2*n+1) 1 (2*j) := by
  unfold lam fermi
  rw [exp_beta]
  simp only [pow_add,pow_mul,neg_one_sq,one_pow,pow_one,mul_neg_one,mul_one]
  push_cast
  have hneg (x : ℂ) : -x-1 = -(x+1) := by ring
  simp only [hneg,mul_neg,div_neg_eq_neg_div]

private theorem fermi_odd (s j : ℕ) :
    fermi s 1 (2*j+1) = (1/(2:ℂ)^s)*fermi s 2 j := by
  unfold fermi
  have hk : 2*j+1+1 = 2*(j+1) := by omega
  rw [hk]
  have he : Real.pi*1*((2*(j+1):ℕ):ℝ) = Real.pi*2*((j+1:ℕ):ℝ) := by push_cast; ring
  rw [he]
  push_cast
  simp only [mul_pow,div_eq_mul_inv,mul_inv_rev]
  ring

private theorem lam_odd (n j : ℕ) :
    lam n ((Real.pi:ℂ)*(1-Complex.I)/2) (2*j+1) = (1/(2:ℂ)^(2*n+1))*bose (2*n+1) 2 j := by
  unfold lam bose
  rw [exp_beta]
  have hk : 2*j+1+1 = 2*(j+1) := by omega
  rw [hk]
  simp only [pow_mul,neg_one_sq,one_pow,mul_one]
  have he : Real.pi*((2*(j+1):ℕ):ℝ) = Real.pi*2*((j+1:ℕ):ℝ) := by push_cast; ring
  rw [he]
  push_cast
  simp only [mul_pow,div_eq_mul_inv,mul_inv_rev]
  ring

private theorem bose_summable (s : ℕ) (r : ℝ) (hr : 0 < r) : Summable (bose s r) :=
  (Complex.ofRealCLM.hasSum (Series.summableS s r hr).hasSum).summable

private theorem fermi_summable (s : ℕ) (r : ℝ) (hr : 0 < r) : Summable (fermi s r) :=
  (Complex.ofRealCLM.hasSum (Series.summableT s r hr).hasSum).summable

private theorem bose_tsum (s : ℕ) (r : ℝ) : (∑' j : ℕ, bose s r j) = (S s r:ℂ) :=
  (Complex.ofReal_tsum _).symm

private theorem fermi_tsum (s : ℕ) (r : ℝ) : (∑' j : ℕ, fermi s r j) = (T s r:ℂ) :=
  (Complex.ofReal_tsum _).symm

/-- Complex Lambert specializations with absolute convergence before parity splitting. -/
theorem lambertParity : Contracts.lambertParity := by
  intro n
  constructor
  · have hα : 0 < ((Real.pi:ℂ)*(1+Complex.I)).re := by simpa using Real.pi_pos
    have hsum := Series.summableL n ((Real.pi:ℂ)*(1+Complex.I)) hα
    have hB := bose_summable (2*n+1) 2 (by norm_num)
    rw [← bose_tsum (2*n+1) 2]
    unfold L
    apply tsum_congr
    intro j
    unfold bose
    rw [exp_alpha]
    push_cast
    congr 3
    congr 1
    ring
  · let β : ℂ := (Real.pi:ℂ)*(1-Complex.I)/2
    have hβ : 0 < β.re := by
      dsimp [β]
      norm_num [Complex.mul_re, Complex.div_re]
      positivity
    have hL : Summable (lam n β) := Series.summableL n β hβ
    have hT := fermi_summable (2*n+1) 1 (by norm_num)
    have hB2 := bose_summable (2*n+1) 2 (by norm_num)
    have hT2 := fermi_summable (2*n+1) 2 (by norm_num)
    have hinjE : Function.Injective (fun j : ℕ => 2*j) := mul_right_injective₀ (by norm_num)
    have hinjO : Function.Injective (fun j : ℕ => 2*j+1) := (add_left_injective 1).comp hinjE
    have hLe : Summable (fun j : ℕ => lam n β (2*j)) := hL.comp_injective hinjE
    have hLo : Summable (fun j : ℕ => lam n β (2*j+1)) := hL.comp_injective hinjO
    have hTe : Summable (fun j : ℕ => fermi (2*n+1) 1 (2*j)) := hT.comp_injective hinjE
    have hTo : Summable (fun j : ℕ => fermi (2*n+1) 1 (2*j+1)) := hT.comp_injective hinjO
    have hLE : (∑' j : ℕ, lam n β (2*j)) = -(∑' j : ℕ, fermi (2*n+1) 1 (2*j)) := by
      calc
        _ = ∑' j : ℕ, -fermi (2*n+1) 1 (2*j) := tsum_congr (lam_even n)
        _ = _ := tsum_neg
    have hLO : (∑' j : ℕ, lam n β (2*j+1)) = (1/(2:ℂ)^(2*n+1))*(S (2*n+1) 2:ℂ) := by
      calc
        _ = ∑' j : ℕ, (1/(2:ℂ)^(2*n+1))*bose (2*n+1) 2 j := tsum_congr (lam_odd n)
        _ = _ := by rw [hB2.tsum_mul_left,bose_tsum]
    have hTO : (∑' j : ℕ, fermi (2*n+1) 1 (2*j+1)) = (1/(2:ℂ)^(2*n+1))*(T (2*n+1) 2:ℂ) := by
      calc
        _ = ∑' j : ℕ, (1/(2:ℂ)^(2*n+1))*fermi (2*n+1) 2 j := tsum_congr (fermi_odd (2*n+1))
        _ = _ := by rw [hT2.tsum_mul_left,fermi_tsum]
    have hLs := tsum_even_add_odd hLe hLo
    have hTs := tsum_even_add_odd hTe hTo
    rw [hLE,hLO] at hLs
    rw [hTO,fermi_tsum] at hTs
    have heven := (eq_sub_iff_add_eq).mpr hTs
    change L n β = _
    change _ = L n β at hLs
    rw [← hLs,heven]
    push_cast
    ring


end Plouffe.Proofs.Parity
