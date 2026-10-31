/-
Copyright (c) 2026 Patrick Lopatto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Lopatto
-/
module

public import Plouffe.Proofs.Gamma.ThetaProduct.Gaussian
public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Tactic.Linarith

public section
namespace Plouffe.Proofs.Gamma.ThetaProduct
open Plouffe.QBinomial

theorem twice_choose_two (k : ℕ) : 2*Nat.choose k 2+k = k^2 := by
  induction k with
  | zero => norm_num
  | succ k ih =>
    have hc : Nat.choose (k+1) 2 = Nat.choose k 2+k := by
      simpa [Nat.add_comm] using Nat.choose_succ_succ k 1
    rw [hc]
    nlinarith

theorem gaussian_symm (Q : ℝ) (n k : ℕ) (hk : k ≤ n) :
    gaussian Q n k = gaussian Q n (n-k) := by
  simp only [gaussian,ite_eq_left hk,ite_eq_left (Nat.sub_le n k),Nat.sub_sub_self hk]
  rw [mul_comm]

/-- The triangular q-binomial weight becomes a square after centering. -/
theorem centered_term (q : ℝ) (hq : q ≠ 0) (n k : ℕ) :
    q^(n^2)*(coefficient (q^2) (2*n) k)*(q^(1-2*(n : ℤ)))^k =
      q^(((k : ℤ)-(n : ℤ))^2)*gaussian (q^2) (2*n) k := by
  have htpow : (q^(1-2*(n : ℤ)))^k = q^((1-2*(n : ℤ))*(k : ℤ)) := by
    rw [← zpow_natCast,← zpow_mul]
  have hc : 2*(Nat.choose k 2 : ℤ)+(k : ℤ) = (k : ℤ)^2 := by
    exact_mod_cast twice_choose_two k
  rw [coefficient,← pow_mul,htpow,← zpow_natCast q (n^2),← zpow_natCast q (2*Nat.choose k 2)]
  calc
    _ = (q^((n^2 : ℕ) : ℤ)*q^((2*Nat.choose k 2 : ℕ) : ℤ)*
        q^((1-2*(n : ℤ))*(k : ℤ)))*gaussian (q^2) (2*n) k := by ring
    _ = q^(((n^2 : ℕ) : ℤ)+((2*Nat.choose k 2 : ℕ) : ℤ)+
        (1-2*(n : ℤ))*(k : ℤ))*gaussian (q^2) (2*n) k := by
      rw [zpow_add₀ hq,zpow_add₀ hq]
    _ = _ := by
      congr 2
      push_cast
      nlinarith

theorem sum_odd (n : ℕ) : (∑ j ∈ Finset.range n, (2*j+1)) = n^2 := by
  induction n with
  | zero => simp
  | succ n ih => rw [Finset.sum_range_succ,ih]; nlinarith

/-- The centered finite q-binomial product is a square of its positive odd factors. -/
theorem centered_product (q : ℝ) (hq : q ≠ 0) (n : ℕ) :
    q^(n^2)*(∏ j ∈ Finset.range (2*n), (1+q^(1-2*(n : ℤ))*(q^2)^j)) =
      (∏ j ∈ Finset.range n, (1+q^(2*j+1)))^2 := by
  let f : ℕ → ℝ := fun j => 1+q^(1-2*(n : ℤ))*(q^2)^j
  have hp (j : ℕ) : f (n+j) = 1+q^(2*j+1) := by
    dsimp [f]
    rw [← pow_mul,← zpow_natCast q (2*(n+j)),← zpow_add₀ hq]
    have he : (1-2*(n : ℤ))+((2*(n+j) : ℕ) : ℤ) = ((2*j+1 : ℕ) : ℤ) := by
      push_cast
      ring
    rw [he,zpow_natCast]
  have hm (j : ℕ) (hj : j ∈ Finset.range n) :
      f (n-1-j) = (1+q^(2*j+1))/q^(2*j+1) := by
    have hjn : j < n := Finset.mem_range.mp hj
    have hn : ((n-1-j : ℕ) : ℤ) = (n : ℤ)-1-(j : ℤ) := by omega
    dsimp [f]
    rw [← pow_mul,← zpow_natCast q (2*(n-1-j)),← zpow_add₀ hq]
    have he : (1-2*(n : ℤ))+((2*(n-1-j) : ℕ) : ℤ) = -((2*j+1 : ℕ) : ℤ) := by
      push_cast
      rw [hn]
      ring
    rw [he,zpow_neg,zpow_natCast]
    field_simp
    ring
  have hneg : (∏ j ∈ Finset.range n, f j) =
      (∏ j ∈ Finset.range n, (1+q^(2*j+1)))/q^(n^2) := by
    rw [← Finset.prod_range_reflect f n,Finset.prod_congr rfl hm,Finset.prod_div_distrib,
      Finset.prod_pow_eq_pow_sum,sum_odd]
  change q^(n^2)*(∏ j ∈ Finset.range (2*n), f j) = _
  rw [show 2*n = n+n by omega,Finset.prod_range_add,hneg,Finset.prod_congr rfl (fun j _ => hp j)]
  field_simp

/-- The symmetric finite Gaussian identity with all sums indexed by natural numbers. -/
theorem finite_centered (q : ℝ) (hq0 : 0 < q) (hq1 : q < 1) (n : ℕ) :
    (∏ j ∈ Finset.range n, (1+q^(2*j+1)))^2 =
      gaussian (q^2) (2*n) n+
        2*∑ j ∈ Finset.range n, q^((j+1)^2)*gaussian (q^2) (2*n) (n+(j+1)) := by
  have hq := ne_of_gt hq0
  have hq2 : q^2 < 1 := pow_lt_one₀ hq0.le hq1 (by norm_num)
  let f : ℕ → ℝ := fun k => q^(n^2)*coefficient (q^2) (2*n) k*(q^(1-2*(n : ℤ)))^k
  let g : ℕ → ℝ := fun k => q^(k^2)*gaussian (q^2) (2*n) (n+k)
  have hs : (∑ k ∈ Finset.range (2*n+1), f k) =
      (∏ j ∈ Finset.range n, (1+q^(2*j+1)))^2 := by
    dsimp [f]
    simp_rw [mul_assoc]
    rw [← Finset.mul_sum,← finite_qbinomial (q^2) (sq_pos_of_pos hq0) hq2,
      centered_product q hq]
  have hp (k : ℕ) : f (n+k) = g k := by
    dsimp [f,g]
    rw [centered_term q hq]
    have he : (((n+k : ℕ) : ℤ)-(n : ℤ))^2 = ((k^2 : ℕ) : ℤ) := by
      push_cast
      ring
    rw [he,zpow_natCast]
  have hm (j : ℕ) (hj : j ∈ Finset.range n) : f (n-1-j) = g (j+1) := by
    have hjn : j < n := Finset.mem_range.mp hj
    have hcast : ((n-1-j : ℕ) : ℤ) = (n : ℤ)-1-(j : ℤ) := by omega
    dsimp [f,g]
    rw [centered_term q hq,gaussian_symm (q^2) (2*n) (n-1-j) (by omega),
      show 2*n-(n-1-j) = n+(j+1) by omega]
    have he : (((n-1-j : ℕ) : ℤ)-(n : ℤ))^2 = (((j+1)^2 : ℕ) : ℤ) := by
      rw [hcast]
      push_cast
      ring
    rw [he,zpow_natCast]
  have hneg : (∑ j ∈ Finset.range n, f j) = ∑ j ∈ Finset.range n, g (j+1) := by
    rw [← Finset.sum_range_reflect f n]
    exact Finset.sum_congr rfl hm
  rw [show 2*n+1 = n+(n+1) by omega,Finset.sum_range_add,hneg,
    Finset.sum_congr rfl (fun k _ => hp k),Finset.sum_range_succ'] at hs
  simpa [g,two_mul,add_assoc,add_comm,add_left_comm] using hs.symm

end Plouffe.Proofs.Gamma.ThetaProduct
