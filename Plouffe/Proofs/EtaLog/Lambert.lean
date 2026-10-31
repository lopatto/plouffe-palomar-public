/-
Copyright (c) 2026 Patrick Lopatto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Lopatto
-/
module

public import Mathlib.Analysis.SpecialFunctions.Log.Deriv
public import Mathlib.Analysis.SpecialFunctions.Log.Summable
public import Mathlib.NumberTheory.TsumDivisorsAntidiagonal
public import Mathlib.Topology.Algebra.InfiniteSum.Real
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Ring

public section
namespace Plouffe.Proofs.EtaLog

private theorem geometric_row (q : ℝ) (hq0 : 0 < q) (hq1 : q < 1) (j : ℕ) :
    HasSum (fun m : ℕ => q^((j+1)*(m+1))/((j+1:ℕ):ℝ))
      (q^(j+1)/(((j+1:ℕ):ℝ)*(1-q^(j+1)))) := by
  have hx0 := pow_pos hq0 (j+1)
  have hx1 := pow_lt_one₀ hq0.le hq1 (Nat.succ_ne_zero j)
  have h := ((hasSum_geometric_of_lt_one hx0.le hx1).mul_left (q^(j+1))).div_const ((j+1:ℕ):ℝ)
  convert h using 1
  · funext m
    rw [pow_mul,pow_succ]
    ring
  · simp only [div_eq_mul_inv,mul_inv_rev]
    ring

private theorem weighted_summable (q : ℝ) (hq0 : 0 < q) (hq1 : q < 1) :
    Summable (fun j : ℕ => q^(j+1)/(((j+1:ℕ):ℝ)*(1-q^(j+1)))) := by
  have hqnorm : ‖q‖ < 1 := by simpa [Real.norm_eq_abs,abs_of_pos hq0] using hq1
  have h := summable_norm_pow_mul_geometric_div_one_sub 0 hqnorm
  simp only [pow_zero,one_mul] at h
  have hs := (summable_nat_add_iff 1).mpr h
  apply hs.of_nonneg_of_le
  · intro j
    have hx1 := pow_lt_one₀ hq0.le hq1 (Nat.succ_ne_zero j)
    positivity
  · intro j
    have hx1 := pow_lt_one₀ hq0.le hq1 (Nat.succ_ne_zero j)
    have hk : (1:ℝ) ≤ ((j+1:ℕ):ℝ) := by exact_mod_cast (Nat.succ_le_succ (Nat.zero_le j))
    exact div_le_div_of_nonneg_left (pow_nonneg hq0.le _)
      (sub_pos.mpr hx1) (by simpa only [one_mul] using mul_le_mul_of_nonneg_right hk (sub_nonneg.mpr hx1.le))

/-- The logarithmic Lambert/product identity, with absolute convergence before exchanging sums. -/
theorem lambert_log (q : ℝ) (hq0 : 0 < q) (hq1 : q < 1) :
    (∑' j : ℕ, q^(j+1)/(((j+1:ℕ):ℝ)*(1-q^(j+1)))) =
      -(∑' m : ℕ, Real.log (1-q^(m+1))) := by
  let d : ℕ × ℕ → ℝ := fun jm => q^((jm.1+1)*(jm.2+1))/((jm.1+1:ℕ):ℝ)
  have hnonneg : 0 ≤ d := by intro jm; dsimp [d]; positivity
  have hrows : ∀ j : ℕ, Summable (fun m : ℕ => d (j,m)) :=
    fun j => (geometric_row q hq0 hq1 j).summable
  have hsumrows : Summable (fun j : ℕ => ∑' m : ℕ, d (j,m)) :=
    (weighted_summable q hq0 hq1).congr (fun j => (geometric_row q hq0 hq1 j).tsum_eq.symm)
  have hdouble : Summable d := (summable_prod_of_nonneg hnonneg).mpr ⟨hrows,hsumrows⟩
  have hlogrow (m : ℕ) : (∑' j : ℕ, d (j,m)) = -Real.log (1-q^(m+1)) := by
    have hx : |q^(m+1)| < 1 := by
      rw [abs_of_pos (pow_pos hq0 _)]
      exact pow_lt_one₀ hq0.le hq1 (Nat.succ_ne_zero m)
    have hlog := Real.hasSum_pow_div_log_of_abs_lt_one hx
    calc
      _ = ∑' j : ℕ, (q^(m+1))^(j+1)/((j+1:ℕ):ℝ) := by
        apply tsum_congr
        intro j
        dsimp [d]
        rw [Nat.mul_comm (j+1) (m+1),pow_mul]
      _ = _ := by simpa only [Nat.cast_add,Nat.cast_one] using hlog.tsum_eq
  calc
    _ = ∑' j : ℕ, ∑' m : ℕ, d (j,m) := tsum_congr (fun j => (geometric_row q hq0 hq1 j).tsum_eq.symm)
    _ = ∑' m : ℕ, ∑' j : ℕ, d (j,m) := hdouble.tsum_comm.symm
    _ = ∑' m : ℕ, -Real.log (1-q^(m+1)) := tsum_congr hlogrow
    _ = _ := tsum_neg


end Plouffe.Proofs.EtaLog
