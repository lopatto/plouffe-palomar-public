/-
Copyright (c) 2026 Patrick Lopatto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Lopatto
-/
module

public import Plouffe.Proofs.Gamma.ThetaProduct.Euler
public import Plouffe.Infrastructure.QBinomial

public section
namespace Plouffe.Proofs.Gamma.ThetaProduct
open Plouffe.QBinomial

@[simp] theorem poch_zero (Q : ℝ) : poch Q 0 = 1 := by simp [poch]

theorem poch_succ (Q : ℝ) (n : ℕ) : poch Q (n+1) = poch Q n*(1-Q^(n+1)) := by
  exact Finset.prod_range_succ _ _

theorem poch_pos (Q : ℝ) (hQ0 : 0 < Q) (hQ1 : Q < 1) (n : ℕ) : 0 < poch Q n := by
  unfold poch
  apply Finset.prod_pos
  intro j hj
  exact sub_pos.mpr (pow_lt_one₀ hQ0.le hQ1 (Nat.succ_ne_zero j))

@[simp] theorem gaussian_zero_right (Q : ℝ) (hQ0 : 0 < Q) (hQ1 : Q < 1) (n : ℕ) :
    gaussian Q n 0 = 1 := by
  simp [gaussian,ne_of_gt (poch_pos Q hQ0 hQ1 n)]

@[simp] theorem gaussian_self (Q : ℝ) (hQ0 : 0 < Q) (hQ1 : Q < 1) (n : ℕ) :
    gaussian Q n n = 1 := by
  simp [gaussian,ne_of_gt (poch_pos Q hQ0 hQ1 n)]

theorem gaussian_eq_zero (Q : ℝ) (n k : ℕ) (h : n < k) : gaussian Q n k = 0 := by
  simp [gaussian,not_le.mpr h]

/-- Pascal's Gaussian recurrence, with every natural subtraction guarded. -/
theorem gaussian_pascal (Q : ℝ) (hQ0 : 0 < Q) (hQ1 : Q < 1) (n k : ℕ) (hk : k ≤ n) :
    gaussian Q (n+1) (k+1) = gaussian Q n (k+1)+Q^(n-k)*gaussian Q n k := by
  by_cases hkn : k = n
  · subst k
    rw [gaussian_self Q hQ0 hQ1 (n+1),gaussian_eq_zero Q n (n+1) (by omega),
      gaussian_self Q hQ0 hQ1 n]
    simp
  · have hlt : k < n := by omega
    let d := n-(k+1)
    have hdiff : n-k = d+1 := by dsimp [d]; omega
    have hsum : (d+1)+(k+1) = n+1 := by dsimp [d]; omega
    have hfac : 1-Q^(n+1) = (1-Q^(d+1))+Q^(d+1)*(1-Q^(k+1)) := by
      rw [← hsum,pow_add]
      ring
    have hPk := ne_of_gt (poch_pos Q hQ0 hQ1 k)
    have hPd := ne_of_gt (poch_pos Q hQ0 hQ1 d)
    have hfk : 1-Q^(k+1) ≠ 0 := ne_of_gt (sub_pos.mpr (pow_lt_one₀ hQ0.le hQ1 (Nat.succ_ne_zero k)))
    have hfd : 1-Q^(d+1) ≠ 0 := ne_of_gt (sub_pos.mpr (pow_lt_one₀ hQ0.le hQ1 (Nat.succ_ne_zero d)))
    simp only [gaussian,ite_eq_left (show k+1 ≤ n+1 by omega),
      ite_eq_left (show k+1 ≤ n by omega),ite_eq_left hk]
    rw [show n+1-(k+1) = n-k by omega,hdiff,show n-(k+1) = d from rfl,
      poch_succ Q n,poch_succ Q k,poch_succ Q d,hfac]
    field_simp

@[simp] theorem coefficient_zero_right (Q : ℝ) (hQ0 : 0 < Q) (hQ1 : Q < 1) (n : ℕ) :
    coefficient Q n 0 = 1 := by simp [coefficient,gaussian_zero_right Q hQ0 hQ1]

theorem coefficient_eq_zero (Q : ℝ) (n k : ℕ) (h : n < k) : coefficient Q n k = 0 := by
  rw [coefficient,gaussian_eq_zero Q n k h,mul_zero]

/-- Multiplication by one more linear factor is the weighted Pascal recurrence. -/
theorem coefficient_pascal (Q : ℝ) (hQ0 : 0 < Q) (hQ1 : Q < 1) (n k : ℕ) (hk : k ≤ n) :
    coefficient Q (n+1) (k+1) = coefficient Q n (k+1)+Q^n*coefficient Q n k := by
  have hchoose : Nat.choose (k+1) 2 = Nat.choose k 2+k := by
    simpa [Nat.add_comm] using Nat.choose_succ_succ k 1
  have hexp : Nat.choose (k+1) 2+(n-k) = n+Nat.choose k 2 := by rw [hchoose]; omega
  have hpow : Q^(Nat.choose (k+1) 2)*Q^(n-k) = Q^n*Q^(Nat.choose k 2) := by
    rw [← pow_add,hexp,pow_add]
  dsimp [coefficient]
  rw [gaussian_pascal Q hQ0 hQ1 n k hk]
  calc
    _ = Q^(Nat.choose (k+1) 2)*gaussian Q n (k+1)+
      (Q^(Nat.choose (k+1) 2)*Q^(n-k))*gaussian Q n k := by ring
    _ = _ := by rw [hpow]; ring

/-- The finite q-binomial identity, obtained from Gaussian Pascal rather than assumed. -/
theorem finite_qbinomial (Q : ℝ) (hQ0 : 0 < Q) (hQ1 : Q < 1) (t : ℝ) (n : ℕ) :
    (∏ j ∈ Finset.range n, (1+t*Q^j)) =
      ∑ k ∈ Finset.range (n+1), coefficient Q n k*t^k := by
  induction n with
  | zero => simp [coefficient,gaussian,poch]
  | succ n ih =>
    have hmiddle (k : ℕ) (hk : k ∈ Finset.range (n+1)) :
        coefficient Q (n+1) (k+1)*t^(k+1) =
          coefficient Q n (k+1)*t^(k+1)+(t*Q^n)*(coefficient Q n k*t^k) := by
      rw [coefficient_pascal Q hQ0 hQ1 n k (by simpa only [Finset.mem_range,Nat.lt_succ_iff] using hk),
        pow_succ]
      ring
    have hfirst : coefficient Q (n+1) 0*t^0 = 1 := by
      simp [coefficient_zero_right Q hQ0 hQ1]
    have hshift : (∑ k ∈ Finset.range (n+1), coefficient Q n (k+1)*t^(k+1))+1 =
        ∑ k ∈ Finset.range (n+1), coefficient Q n k*t^k := by
      have hs := Finset.sum_range_succ' (fun k => coefficient Q n k*t^k) (n+1)
      rw [Finset.sum_range_succ,coefficient_eq_zero Q n (n+1) (by omega),zero_mul,add_zero,
        coefficient_zero_right Q hQ0 hQ1,pow_zero,mul_one] at hs
      exact hs.symm
    symm
    rw [Finset.sum_range_succ',hfirst,
      Finset.sum_congr rfl hmiddle,Finset.sum_add_distrib,← Finset.mul_sum]
    calc
      _ = ((∑ k ∈ Finset.range (n+1), coefficient Q n (k+1)*t^(k+1))+1)+
          (t*Q^n)*(∑ k ∈ Finset.range (n+1), coefficient Q n k*t^k) := by ring
      _ = (∑ k ∈ Finset.range (n+1), coefficient Q n k*t^k)*(1+t*Q^n) := by
        rw [hshift]
        ring
      _ = _ := by rw [Finset.prod_range_succ,ih]

end Plouffe.Proofs.Gamma.ThetaProduct
