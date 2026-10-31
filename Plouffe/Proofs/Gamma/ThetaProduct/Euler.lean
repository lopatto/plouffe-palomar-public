/-
Copyright (c) 2026 Patrick Lopatto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Lopatto
-/
module

public import Plouffe.Proofs.EtaRatio.Euler
public import Mathlib.Tactic.FieldSimp

public section
namespace Plouffe.Proofs.Gamma.ThetaProduct

/-- The convergent odd positive factors in the Jacobi product, independently of any theta identity. -/
theorem odd_factor_multipliable (q : ℝ) (hq : |q| < 1) :
    Multipliable (fun j : ℕ => 1+q^(2*j+1)) := by
  have hs : Summable (fun j : ℕ => q^j) := summable_geometric_of_abs_lt_one hq
  have hinj : Function.Injective (fun j : ℕ => 2*j+1) := by
    intro j k h
    change 2*j+1 = 2*k+1 at h
    omega
  exact Real.multipliable_one_add_of_summable (hs.comp_injective hinj)

/-- All factors of the Jacobi Euler product converge; no series/product equality is assumed. -/
theorem jacobi_product_multipliable (q : ℝ) (hq : |q| < 1) :
    Multipliable (fun j : ℕ => (1-q^(2*(j+1)))*(1+q^(2*j+1))^2) := by
  have hq2 : |q^2| < 1 := by
    rw [abs_pow]
    exact pow_lt_one₀ (abs_nonneg q) hq (by norm_num)
  have he : Multipliable (fun j : ℕ => 1-q^(2*(j+1))) := by
    simpa only [pow_mul] using EtaRatio.euler_multipliable (q^2) hq2
  have ho := odd_factor_multipliable q hq
  exact he.mul (ho.pow 2)

/-- Parity splitting evaluates the Jacobi product in terms of ordinary Euler products. -/
theorem jacobi_product_eq_euler (q : ℝ) (hq : |q| < 1) :
    (∏' j : ℕ, (1-q^(2*(j+1)))*(1+q^(2*j+1))^2) =
      EtaRatio.euler (-q)^2/EtaRatio.euler (q^2) := by
  have hq2 : |q^2| < 1 := by
    rw [abs_pow]
    exact pow_lt_one₀ (abs_nonneg q) hq (by norm_num)
  have hE := EtaRatio.euler_multipliable (q^2) hq2
  have hO := odd_factor_multipliable q hq
  have he : Multipliable (fun j : ℕ => 1-q^(2*(j+1))) := by
    simpa only [pow_mul] using hE
  have hfE (j : ℕ) : 1-(-q)^(2*j+1) = 1+q^(2*j+1) := by
    simp [pow_add,pow_mul]
  have hfO (j : ℕ) : 1-(-q)^(2*j+1+1) = 1-(q^2)^(j+1) := by
    rw [show 2*j+1+1 = 2*(j+1) by omega,pow_mul]
    simp only [neg_sq]
  have hME : Multipliable (fun j : ℕ => 1-(-q)^(2*j+1)) :=
    hO.congr (fun j => (hfE j).symm)
  have hMO : Multipliable (fun j : ℕ => 1-(-q)^(2*j+1+1)) :=
    hE.congr (fun j => (hfO j).symm)
  have hsplit := tprod_even_mul_odd (f := fun j : ℕ => 1-(-q)^(j+1)) hME hMO
  have hodd : (∏' j : ℕ, (1+q^(2*j+1)))*EtaRatio.euler (q^2) = EtaRatio.euler (-q) := by
    simpa only [hfE,hfO,EtaRatio.euler] using hsplit
  have hnonzero : EtaRatio.euler (q^2) ≠ 0 := ne_of_gt (EtaRatio.euler_pos (q^2) hq2)
  have hprod : (∏' j : ℕ, (1-q^(2*(j+1)))*(1+q^(2*j+1))^2) =
      EtaRatio.euler (q^2)*(∏' j : ℕ, (1+q^(2*j+1)))^2 := by
    rw [he.tprod_mul (hO.pow 2),hO.tprod_pow]
    congr 1
    unfold EtaRatio.euler
    apply tprod_congr
    intro j
    rw [pow_mul]
  rw [hprod]
  apply (eq_div_iff hnonzero).2
  rw [← hodd]
  ring

end Plouffe.Proofs.Gamma.ThetaProduct
