/-
Copyright (c) 2026 Patrick Lopatto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Lopatto
-/
module

public import Plouffe.Infrastructure.QBinomial
public import Mathlib.Analysis.SpecialFunctions.Log.Summable
public import Mathlib.Topology.Algebra.InfiniteSum.Order
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.FieldSimp

@[expose] public section
namespace Plouffe.Proofs.Gamma.ThetaProductLimits
open Plouffe.QBinomial Filter
open scoped Topology

/-- The convergent Euler product appearing in the Gaussian coefficient normalization. -/
noncomputable def product (Q : ℝ) : ℝ := ∏' j : ℕ, (1-Q^(j+1))

private theorem factor_pos (Q : ℝ) (hQ0 : 0 < Q) (hQ1 : Q < 1) (j : ℕ) :
    0 < 1-Q^(j+1) := sub_pos.mpr (pow_lt_one₀ hQ0.le hQ1 (Nat.succ_ne_zero j))

theorem product_multipliable (Q : ℝ) (hQ0 : 0 < Q) (hQ1 : Q < 1) :
    Multipliable (fun j : ℕ => 1-Q^(j+1)) := by
  have hs := (summable_nat_add_iff 1).mpr (summable_geometric_of_abs_lt_one
    (by rwa [abs_of_pos hQ0] : |Q| < 1))
  simpa only [sub_eq_add_neg] using Real.multipliable_one_add_of_summable hs.neg

theorem product_pos (Q : ℝ) (hQ0 : 0 < Q) (hQ1 : Q < 1) : 0 < product Q := by
  have hs := (summable_nat_add_iff 1).mpr (summable_geometric_of_abs_lt_one
    (by rwa [abs_of_pos hQ0] : |Q| < 1))
  have hl : Summable (fun j : ℕ => Real.log (1-Q^(j+1))) := by
    simpa only [sub_eq_add_neg] using Real.summable_log_one_add_of_summable hs.neg
  rw [product,← Real.rexp_tsum_eq_tprod (factor_pos Q hQ0 hQ1) hl]
  exact Real.exp_pos _

theorem poch_pos (Q : ℝ) (hQ0 : 0 < Q) (hQ1 : Q < 1) (n : ℕ) : 0 < poch Q n := by
  exact Finset.prod_pos (fun j _ => factor_pos Q hQ0 hQ1 j)

theorem poch_antitone (Q : ℝ) (hQ0 : 0 < Q) (hQ1 : Q < 1) : Antitone (poch Q) := by
  apply antitone_nat_of_succ_le
  intro n
  have hs : poch Q (n+1) = poch Q n*(1-Q^(n+1)) := Finset.prod_range_succ _ _
  rw [hs]
  apply mul_le_of_le_one_right (poch_pos Q hQ0 hQ1 n).le
  have hp := pow_nonneg hQ0.le (n+1)
  linarith

theorem poch_tendsto (Q : ℝ) (hQ0 : 0 < Q) (hQ1 : Q < 1) :
    Tendsto (poch Q) atTop (𝓝 (product Q)) :=
  (product_multipliable Q hQ0 hQ1).hasProd.tendsto_prod_nat

theorem product_le_poch (Q : ℝ) (hQ0 : 0 < Q) (hQ1 : Q < 1) (n : ℕ) :
    product Q ≤ poch Q n :=
  (poch_antitone Q hQ0 hQ1).le_of_tendsto (poch_tendsto Q hQ0 hQ1) n

theorem poch_le_one (Q : ℝ) (hQ0 : 0 < Q) (hQ1 : Q < 1) (n : ℕ) : poch Q n ≤ 1 := by
  simpa only [poch,Finset.range_zero,Finset.prod_empty] using poch_antitone Q hQ0 hQ1 (Nat.zero_le n)

/-- A uniform positive Gaussian-coefficient bound; no series/product identity is used. -/
theorem gaussian_bounds (Q : ℝ) (hQ0 : 0 < Q) (hQ1 : Q < 1) (N k : ℕ) :
    0 ≤ gaussian Q N k ∧ gaussian Q N k ≤ 1/(product Q)^2 := by
  by_cases hk : k ≤ N
  · rw [gaussian,ite_eq_left hk]
    have hp := product_pos Q hQ0 hQ1
    have hd : 0 < poch Q k*poch Q (N-k) := mul_pos (poch_pos Q hQ0 hQ1 k) (poch_pos Q hQ0 hQ1 (N-k))
    refine ⟨div_nonneg (poch_pos Q hQ0 hQ1 N).le hd.le,?_⟩
    apply div_le_div₀ (by norm_num : (0:ℝ) ≤ 1) (poch_le_one Q hQ0 hQ1 N) (sq_pos_of_pos hp)
    simpa only [pow_two] using mul_le_mul (product_le_poch Q hQ0 hQ1 k)
      (product_le_poch Q hQ0 hQ1 (N-k)) hp.le (poch_pos Q hQ0 hQ1 k).le
  · rw [gaussian,ite_eq_right hk]
    exact ⟨le_rfl,by positivity⟩

/-- Both denominator indices tend to infinity for every fixed signed central offset. -/
theorem offset_indices_tendsto (k : ℤ) :
    Tendsto (fun n : ℕ => ((n:ℤ)+k).toNat) atTop atTop ∧
    Tendsto (fun n : ℕ => 2*n-((n:ℤ)+k).toNat) atTop atTop := by
  have hk1 : k ≤ (k.natAbs:ℤ) := Int.le_natAbs
  have hk2 : -(k.natAbs:ℤ) ≤ k  := by
    have h : -k ≤ ((-k).natAbs:ℤ) := Int.le_natAbs
    rw [Int.natAbs_neg] at h
    omega
  constructor
  · apply tendsto_atTop.2
    intro b
    refine eventually_atTop.2 ⟨b+k.natAbs,?_⟩
    intro n hn
    omega
  · apply tendsto_atTop.2
    intro b
    refine eventually_atTop.2 ⟨b+k.natAbs,?_⟩
    intro n hn
    omega

/-- The central Gaussian quotient tends to its Euler normalization for every integer offset. -/
theorem gaussian_center_tendsto (Q : ℝ) (hQ0 : 0 < Q) (hQ1 : Q < 1) (k : ℤ) :
    Tendsto (fun n : ℕ => gaussian Q (2*n) (((n:ℤ)+k).toNat)) atTop (𝓝 (1/product Q)) := by
  have hP := poch_tendsto Q hQ0 hQ1
  have h2 : Tendsto (fun n : ℕ => 2*n) atTop atTop :=
    tendsto_atTop_mono (fun n => by change n ≤ 2*n; omega) tendsto_id
  have hi := offset_indices_tendsto k
  have hp := product_pos Q hQ0 hQ1
  have hlim := (hP.comp h2).div ((hP.comp hi.1).mul (hP.comp hi.2)) (mul_ne_zero hp.ne' hp.ne')
  have hval : product Q/(product Q*product Q) = 1/product Q := by field_simp
  rw [hval] at hlim
  apply hlim.congr'
  have hk1 : k ≤ (k.natAbs:ℤ) := Int.le_natAbs
  have hk2 : -(k.natAbs:ℤ) ≤ k  := by
    have h : -k ≤ ((-k).natAbs:ℤ) := Int.le_natAbs
    rw [Int.natAbs_neg] at h
    omega
  filter_upwards [eventually_ge_atTop k.natAbs] with n hn
  have hg : ((n:ℤ)+k).toNat ≤ 2*n := by omega
  rw [gaussian,ite_eq_left hg]
  rfl

/-- Natural offsets are the direct input to the centered finite q-binomial identity. -/
theorem gaussian_center_nat_tendsto (Q : ℝ) (hQ0 : 0 < Q) (hQ1 : Q < 1) (k : ℕ) :
    Tendsto (fun n : ℕ => gaussian Q (2*n) (n+k)) atTop (𝓝 (1/product Q)) := by
  simpa only [← Int.natCast_add,Int.toNat_natCast] using gaussian_center_tendsto Q hQ0 hQ1 (k:ℤ)

#print axioms product_pos
#print axioms poch_tendsto
#print axioms gaussian_bounds
#print axioms gaussian_center_tendsto

end Plouffe.Proofs.Gamma.ThetaProductLimits
