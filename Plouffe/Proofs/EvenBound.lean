/-
Copyright (c) 2026 Patrick Lopatto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Lopatto
-/
module

public import Plouffe.Proofs.Signs
public import Plouffe.Proofs.Vepstas

public section
namespace Plouffe.Proofs.EvenBound

/-- The quantitative bound used for the paper's even denominator estimate. -/
theorem evenCombinationBound (s : ℕ) (p q : ℝ) (hp : 16 ≤ p) (hq : 4 ≤ |q|) :
    -p*(S s 1-S s 2)+(S s 2-S s 4)/(2*q+1) ≤
      -16*(S s 1-S s 2)+(S s 2-S s 4)/7 := by
  obtain ⟨hd2,horder⟩ := Signs.deltaOrder s
  have hd1 : 0 ≤ S s 1-S s 2 := (hd2.trans horder).le
  have hpterm : 16*(S s 1-S s 2) ≤ p*(S s 1-S s 2) :=
    mul_le_mul_of_nonneg_right hp hd1
  have hfrac : (S s 2-S s 4)/(2*q+1) ≤ (S s 2-S s 4)/7 := by
    by_cases hq0 : 0 ≤ q
    · rw [abs_of_nonneg hq0] at hq
      exact div_le_div_of_nonneg_left hd2.le (by norm_num) (by linarith)
    · rw [abs_of_neg (lt_of_not_ge hq0)] at hq
      have hneg : (S s 2-S s 4)/(2*q+1) < 0 :=
        div_neg_of_pos_of_neg hd2 (by linarith)
      exact hneg.le.trans (div_nonneg hd2.le (by norm_num))
  linarith

/-- The paper's displayed quantitative upper bound for the even denominator. -/
theorem evenDenominatorBound (m : ℕ) (hm : 1 ≤ m) :
    (E m:ℝ)*Real.pi^(4*m+1) ≤
      -16*(S (4*m+1) 1-S (4*m+1) 2)+(S (4*m+1) 2-S (4*m+1) 4)/7 := by
  obtain ⟨_,_,_,_,hp,hq,hk1,hk2⟩ := Elementary.kCoefficients m hm
  have hu := Vepstas.evenData m hm
  have hbound := evenCombinationBound (4*m+1) ((16:ℝ)^m) ((-4:ℝ)^m) hp hq
  rw [hu,hk1,hk2]
  convert hbound using 1; ring

#print axioms evenCombinationBound
#print axioms evenDenominatorBound

end Plouffe.Proofs.EvenBound
