/-
Copyright (c) 2026 Patrick Lopatto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Lopatto
-/
module

public import Plouffe.Proofs.Series
public import Plouffe.Proofs.Elementary

public section
namespace Plouffe.Proofs.Signs

private noncomputable def term (s : ℕ) (r : ℝ) (j : ℕ) : ℝ :=
  1 / (((j+1:ℕ):ℝ)^s*(Real.exp (Real.pi*r*((j+1:ℕ):ℝ))-1))

private theorem term_summable (s : ℕ) (r : ℝ) (hr : 0 < r) : Summable (term s r) :=
  Series.summableS s r hr

private theorem exp_scales (j : ℕ) :
    Real.exp (Real.pi*2*((j+1:ℕ):ℝ)) = Real.exp (Real.pi*((j+1:ℕ):ℝ))^2 ∧
    Real.exp (Real.pi*4*((j+1:ℕ):ℝ)) = Real.exp (Real.pi*((j+1:ℕ):ℝ))^4 := by
  constructor
  · rw [show Real.pi*2*((j+1:ℕ):ℝ) = (2:ℕ)*(Real.pi*((j+1:ℕ):ℝ)) by push_cast; ring,
      Real.exp_nat_mul]
  · rw [show Real.pi*4*((j+1:ℕ):ℝ) = (4:ℕ)*(Real.pi*((j+1:ℕ):ℝ)) by push_cast; ring,
      Real.exp_nat_mul]

private theorem odd_term_positive (s j : ℕ) (q : ℝ) (hq : 4 ≤ q) :
    0 < q*term s 1 j-(q+1)*term s 2 j+term s 4 j := by
  have ht : 1 < Real.exp (Real.pi*((j+1:ℕ):ℝ)) :=
    Real.one_lt_exp_iff.mpr (mul_pos Real.pi_pos (by positivity))
  have hk := Elementary.oddKernel q (Real.exp (Real.pi*((j+1:ℕ):ℝ))) hq ht
  have hsc := exp_scales j
  have he : q*term s 1 j-(q+1)*term s 2 j+term s 4 j =
      (1/((j+1:ℕ):ℝ)^s)*(q/(Real.exp (Real.pi*((j+1:ℕ):ℝ))-1)-
      (q+1)/(Real.exp (Real.pi*((j+1:ℕ):ℝ))^2-1)+1/(Real.exp (Real.pi*((j+1:ℕ):ℝ))^4-1)) := by
    unfold term
    rw [hsc.1,hsc.2]
    simp only [mul_one, div_eq_mul_inv, mul_inv_rev]
    ring
  rw [he,hk.1]
  exact mul_pos (one_div_pos.mpr (pow_pos (by positivity) s)) hk.2

/-- The odd denominator combination is a sum of strictly positive convergent terms. -/
theorem oddCombinationPositive : Contracts.oddCombinationPositive := by
  intro s q hq
  have h1 := term_summable s 1 (by norm_num)
  have h2 := term_summable s 2 (by norm_num)
  have h4 := term_summable s 4 (by norm_num)
  have hs := ((h1.mul_left q).sub (h2.mul_left (q+1))).add h4
  have hp := hs.tsum_pos (fun j => (odd_term_positive s j q hq).le) 0 (odd_term_positive s 0 q hq)
  rw [Summable.tsum_add ((h1.mul_left q).sub (h2.mul_left (q+1))) h4,
    Summable.tsum_sub (h1.mul_left q) (h2.mul_left (q+1)),h1.tsum_mul_left,h2.tsum_mul_left] at hp
  exact hp

private theorem delta_term_lt (s j : ℕ) :
    term s 2 j-term s 4 j < term s 1 j-term s 2 j := by
  let t := Real.exp (Real.pi*((j+1:ℕ):ℝ))
  have ht : 1 < t := Real.one_lt_exp_iff.mpr (mul_pos Real.pi_pos (by positivity))
  have h2 : 0 < t^2-1 := by nlinarith
  have h4 : t^2-1 < t^4-1 := by nlinarith [sq_nonneg (t^2-1)]
  have hdiff : 0 < 1/(t^2-1)-1/(t^4-1) := sub_pos.mpr (one_div_lt_one_div_of_lt h2 h4)
  have hk := Elementary.deltaKernel t ht
  have he := (div_eq_iff (ne_of_gt hdiff)).mp hk.1
  have hlt : 1/(t^2-1)-1/(t^4-1) < 1/(t-1)-1/(t^2-1) := by
    nlinarith [mul_pos (show 0 < (t+t⁻¹)-1 by linarith [hk.2]) hdiff]
  have hsc := exp_scales j
  have he2 : term s 2 j-term s 4 j =
      (1/((j+1:ℕ):ℝ)^s)*(1/(t^2-1)-1/(t^4-1)) := by
    unfold term
    rw [hsc.1,hsc.2]
    simp only [t,div_eq_mul_inv,mul_inv_rev]
    ring
  have he1 : term s 1 j-term s 2 j =
      (1/((j+1:ℕ):ℝ)^s)*(1/(t-1)-1/(t^2-1)) := by
    unfold term
    rw [hsc.1]
    simp only [t,mul_one,div_eq_mul_inv,mul_inv_rev]
    ring
  rw [he2,he1]
  exact mul_lt_mul_of_pos_left hlt (one_div_pos.mpr (pow_pos (by positivity) s))

/-- Consecutive positive series differences decrease strictly under doubling. -/
theorem deltaOrder : Contracts.deltaOrder := by
  intro s
  constructor
  · exact sub_pos.mpr (Series.strictParameter s 2 4 (by norm_num) (by norm_num))
  · have h1 := term_summable s 1 (by norm_num)
    have h2 := term_summable s 2 (by norm_num)
    have h4 := term_summable s 4 (by norm_num)
    have h := Summable.tsum_lt_tsum (fun j => (delta_term_lt s j).le) (delta_term_lt s 0)
      (h2.sub h4) (h1.sub h2)
    rw [h2.tsum_sub h4,h1.tsum_sub h2] at h
    exact h

/-- The even denominator combination is negative for every allowed signed coefficient. -/
theorem evenCombinationNegative : Contracts.evenCombinationNegative := by
  intro s p q hp hq
  obtain ⟨hd2,horder⟩ := deltaOrder s
  have hd1 : 0 < S s 1-S s 2 := hd2.trans horder
  have hpd : S s 1-S s 2 < p*(S s 1-S s 2) := by
    simpa only [one_mul] using mul_lt_mul_of_pos_right (show 1 < p by linarith) hd1
  by_cases hq0 : 0 ≤ q
  · rw [abs_of_nonneg hq0] at hq
    have hdiv : (S s 2-S s 4)/(2*q+1) ≤ S s 2-S s 4 :=
      div_le_self hd2.le (by linarith)
    linarith
  · rw [abs_of_neg (lt_of_not_ge hq0)] at hq
    have hdiv : (S s 2-S s 4)/(2*q+1) < 0 := div_neg_of_pos_of_neg hd2 (by linarith)
    have hprod : 0 < p*(S s 1-S s 2) := mul_pos (by linarith) hd1
    linarith


end Plouffe.Proofs.Signs
