/-
Copyright (c) 2026 Patrick Lopatto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Lopatto
-/
module

public import Mathlib.Analysis.SpecialFunctions.Log.Summable
public import Mathlib.Topology.Algebra.InfiniteSum.NatInt
public import Mathlib.Tactic.Ring

public section
namespace Plouffe.Proofs.EtaRatio

/-- The ordinary Euler product, with positive successor indexing. -/
@[expose] noncomputable def euler (q : ℝ) : ℝ := ∏' j : ℕ, (1-q^(j+1))

private theorem factor_pos (q : ℝ) (hq : |q| < 1) (j : ℕ) : 0 < 1-q^(j+1) := by
  have h := pow_lt_one₀ (abs_nonneg q) hq (Nat.succ_ne_zero j)
  rw [← abs_pow] at h
  exact sub_pos.mpr ((le_abs_self _).trans_lt h)

/-- Convergence of the Euler product throughout the real open unit interval. -/
theorem euler_multipliable (q : ℝ) (hq : |q| < 1) : Multipliable (fun j : ℕ => 1-q^(j+1)) := by
  have hs := (summable_nat_add_iff 1).mpr (summable_geometric_of_abs_lt_one hq)
  simpa only [sub_eq_add_neg] using Real.multipliable_one_add_of_summable hs.neg

/-- The real Euler product is strictly positive for |q|<1. -/
theorem euler_pos (q : ℝ) (hq : |q| < 1) : 0 < euler q := by
  have hs := (summable_nat_add_iff 1).mpr (summable_geometric_of_abs_lt_one hq)
  have hl : Summable (fun j : ℕ => Real.log (1-q^(j+1))) := by
    simpa only [sub_eq_add_neg] using Real.summable_log_one_add_of_summable hs.neg
  rw [euler,← Real.rexp_tsum_eq_tprod (factor_pos q hq) hl]
  exact Real.exp_pos _

/-- Euler product duplication, proved by convergent even/odd product splitting. -/
theorem euler_duplication (q : ℝ) (hq : |q| < 1) :
    euler q*euler (-q)*euler (q^4) = (euler (q^2))^3 := by
  have hq2 : |q^2| < 1 := by rw [abs_pow]; exact pow_lt_one₀ (abs_nonneg q) hq (by norm_num)
  have hq4 : |q^4| < 1 := by rw [abs_pow]; exact pow_lt_one₀ (abs_nonneg q) hq (by norm_num)
  have hP := euler_multipliable q hq
  have hM := euler_multipliable (-q) (by simpa only [abs_neg] using hq)
  have hP2 := euler_multipliable (q^2) hq2
  have hP4 := euler_multipliable (q^4) hq4
  let f : ℕ → ℝ := fun j => (1-q^(j+1))*(1-(-q)^(j+1))
  have hinjE : Function.Injective (fun j : ℕ => 2*j) := mul_right_injective₀ (by norm_num)
  have hinjO : Function.Injective (fun j : ℕ => 2*j+1) := (add_left_injective 1).comp hinjE
  have hfE (j : ℕ) : f (2*j) = 1-(q^2)^(2*j+1) := by
    dsimp [f]
    have hn : (-q)^(2*j+1) = -q^(2*j+1) := by simp [pow_add,pow_mul]
    have hp : (q^(2*j+1))^2 = (q^2)^(2*j+1) := by rw [← pow_mul,← pow_mul,Nat.mul_comm]
    rw [hn,← hp]
    ring
  have hfO (j : ℕ) : f (2*j+1) = (1-(q^2)^(j+1))^2 := by
    dsimp [f]
    rw [show 2*j+1+1 = 2*(j+1) by omega]
    simp only [pow_mul,neg_sq]
    ring
  have hgO (j : ℕ) : 1-(q^2)^(2*j+1+1) = 1-(q^4)^(j+1) := by
    congr 1
    rw [← pow_mul,← pow_mul]
    congr 1
    omega
  have hgeo : Summable (fun j : ℕ => (q^2)^j) :=
    summable_geometric_of_abs_lt_one hq2
  have hgLe : Multipliable (fun j : ℕ => 1-(q^2)^(2*j+1)) := by
    simpa only [sub_eq_add_neg,Function.comp_apply] using Real.multipliable_one_add_of_summable (hgeo.comp_injective hinjO).neg
  have hgLo : Multipliable (fun j : ℕ => 1-(q^2)^(2*j+1+1)) := hP4.congr (fun j => (hgO j).symm)
  have hfLe : Multipliable (fun j : ℕ => f (2*j)) := hgLe.congr (fun j => (hfE j).symm)
  have hsquare : Multipliable (fun j : ℕ => (1-(q^2)^(j+1))^2) := by
    simpa only [pow_two] using hP2.mul hP2
  have hfLo : Multipliable (fun j : ℕ => f (2*j+1)) := hsquare.congr (fun j => (hfO j).symm)
  have hfs := tprod_even_mul_odd (f := f) hfLe hfLo
  have hgs := tprod_even_mul_odd (f := fun j : ℕ => 1-(q^2)^(j+1)) hgLe hgLo
  have hE : (∏' j : ℕ, f (2*j)) = ∏' j : ℕ, (1-(q^2)^(2*j+1)) := tprod_congr hfE
  have hO : (∏' j : ℕ, f (2*j+1)) = (euler (q^2))^2 := by
    rw [tprod_congr hfO,hP2.tprod_pow]
    rfl
  have hg : (∏' j : ℕ, (1-(q^2)^(2*j+1+1))) = euler (q^4) := tprod_congr hgO
  rw [hE,hO,hP.tprod_mul hM] at hfs
  rw [hg] at hgs
  change _*euler (q^4) = euler (q^2) at hgs
  change _ = euler q*euler (-q) at hfs
  calc
    _ = ((∏' j : ℕ, (1-(q^2)^(2*j+1)))*euler (q^4))*(euler (q^2))^2 := by rw [← hfs]; ring
    _ = _ := by rw [hgs]; ring


end Plouffe.Proofs.EtaRatio
