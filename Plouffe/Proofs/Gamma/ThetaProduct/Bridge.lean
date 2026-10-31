/-
Copyright (c) 2026 Patrick Lopatto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Lopatto
-/
module

public import Plouffe.Proofs.Gamma.ThetaProduct.Centered
public import Plouffe.Proofs.Gamma.ThetaProductLimits
public import Mathlib.Analysis.Normed.Group.Tannery

public section
namespace Plouffe.Proofs.Gamma.ThetaProduct
open Plouffe.QBinomial Filter
open scoped Topology

theorem gaussian_powers_summable (q : ℝ) (hq0 : 0 < q) (hq1 : q < 1) :
    Summable (fun j : ℕ => q^((j+1)^2)) := by
  have hs := summable_geometric_of_abs_lt_one (by rwa [abs_of_pos hq0] : |q| < 1)
  apply hs.of_norm_bounded
  intro j
  rw [Real.norm_of_nonneg (pow_nonneg hq0.le _)]
  exact pow_le_pow_of_le_one hq0.le hq1.le (by nlinarith)

/-- The Gaussian sum/product bridge, proved by a dominated limit of finite identities. -/
theorem gaussian_product (q : ℝ) (hq0 : 0 < q) (hq1 : q < 1) :
    ThetaProductLimits.product (q^2)*(∏' j : ℕ, (1+q^(2*j+1)))^2 =
      1+2*∑' j : ℕ, q^((j+1)^2) := by
  have hQ0 : 0 < q^2 := sq_pos_of_pos hq0
  have hQ1 : q^2 < 1 := pow_lt_one₀ hq0.le hq1 (by norm_num)
  let P := ThetaProductLimits.product (q^2)
  have hP : 0 < P := ThetaProductLimits.product_pos (q^2) hQ0 hQ1
  let f : ℕ → ℕ → ℝ := fun n j => q^((j+1)^2)*gaussian (q^2) (2*n) (n+(j+1))
  have hs := gaussian_powers_summable q hq0 hq1
  have hbound : Summable (fun j : ℕ => q^((j+1)^2)*(1/P^2)) := hs.mul_right _
  have hlim : Tendsto (fun n : ℕ => ∑' j : ℕ, f n j) atTop
      (𝓝 (∑' j : ℕ, q^((j+1)^2)*(1/P))) := by
    apply tendsto_tsum_of_dominated_convergence hbound
    · intro j
      exact tendsto_const_nhds.mul
        (ThetaProductLimits.gaussian_center_nat_tendsto (q^2) hQ0 hQ1 (j+1))
    · apply Eventually.of_forall
      intro n j
      have hb := ThetaProductLimits.gaussian_bounds (q^2) hQ0 hQ1 (2*n) (n+(j+1))
      rw [Real.norm_of_nonneg (mul_nonneg (pow_nonneg hq0.le _) hb.1)]
      exact mul_le_mul_of_nonneg_left hb.2 (pow_nonneg hq0.le _)
  have hf (n : ℕ) : (∑' j : ℕ, f n j) = ∑ j ∈ Finset.range n, f n j := by
    apply tsum_eq_sum
    intro j hj
    have hjn : n ≤ j := Nat.le_of_not_gt (by simpa only [Finset.mem_range] using hj)
    dsimp [f]
    rw [gaussian_eq_zero (q^2) (2*n) (n+(j+1)) (by omega),mul_zero]
  have hfinite (n : ℕ) : (∏ j ∈ Finset.range n, (1+q^(2*j+1)))^2 =
      gaussian (q^2) (2*n) n+2*(∑' j : ℕ, f n j) := by
    rw [hf]
    exact finite_centered q hq0 hq1 n
  have hO := odd_factor_multipliable q (by rwa [abs_of_pos hq0])
  have hleft := hO.hasProd.tendsto_prod_nat.pow 2
  have hright := (ThetaProductLimits.gaussian_center_nat_tendsto (q^2) hQ0 hQ1 0).add
    ((tendsto_const_nhds (x := (2:ℝ))).mul hlim)
  simp only [Nat.add_zero] at hright
  have heq : (∏' j : ℕ, (1+q^(2*j+1)))^2 = 1/P+2*(∑' j : ℕ, q^((j+1)^2)*(1/P)) := by
    apply tendsto_nhds_unique hleft
    exact hright.congr' (Eventually.of_forall (fun n => (hfinite n).symm))
  rw [hs.tsum_mul_right] at heq
  change P*(∏' j : ℕ, (1+q^(2*j+1)))^2 = _
  rw [heq]
  field_simp

/-- Jacobi's Gaussian product at every positive real nome. -/
theorem jacobi_product_eq_gaussian (q : ℝ) (hq0 : 0 < q) (hq1 : q < 1) :
    (∏' j : ℕ, (1-q^(2*(j+1)))*(1+q^(2*j+1))^2) =
      1+2*∑' j : ℕ, q^((j+1)^2) := by
  have hQ0 : 0 < q^2 := sq_pos_of_pos hq0
  have hQ1 : q^2 < 1 := pow_lt_one₀ hq0.le hq1 (by norm_num)
  have he : Multipliable (fun j : ℕ => 1-q^(2*(j+1))) := by
    simpa only [pow_mul] using ThetaProductLimits.product_multipliable (q^2) hQ0 hQ1
  have ho := odd_factor_multipliable q (by rwa [abs_of_pos hq0])
  rw [he.tprod_mul (ho.pow 2),ho.tprod_pow]
  simpa only [pow_mul,ThetaProductLimits.product] using gaussian_product q hq0 hq1

end Plouffe.Proofs.Gamma.ThetaProduct
