/-
Copyright (c) 2026 Patrick Lopatto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Lopatto
-/
module

public import Plouffe.Contracts
public import Plouffe.Infrastructure.Algebra

public section
namespace Plouffe

/-- Explicit intermediate propositions. This data interface itself supplies no proofs. -/
structure Evidence : Prop where
  summableS : Plouffe.Contracts.summableS
  summableT : Plouffe.Contracts.summableT
  positive : Plouffe.Contracts.positive
  strictParameter : Plouffe.Contracts.strictParameter
  fermiBose : Plouffe.Contracts.fermiBose
  lambertReal : Plouffe.Contracts.lambertReal
  summableL : Plouffe.Contracts.summableL
  zetaReal : Plouffe.Contracts.zetaReal
  zetaPositiveSeries : Plouffe.Contracts.zetaPositiveSeries
  finitePartialFractions : Plouffe.Contracts.finitePartialFractions
  cothKernel : Plouffe.Contracts.cothKernel
  doubleSummable : Plouffe.Contracts.doubleSummable
  ramanujanComplex : Plouffe.Contracts.ramanujanComplex
  ramanujanReal : Plouffe.Contracts.ramanujanReal
  center : Plouffe.Contracts.center
  oddCenter : Plouffe.Contracts.oddCenter
  oddScale : Plouffe.Contracts.oddScale
  oddData : Plouffe.Contracts.oddData
  oddKernel : Plouffe.Contracts.oddKernel
  oddCombinationPositive : Plouffe.Contracts.oddCombinationPositive
  oddCoefficients : Plouffe.Contracts.oddCoefficients
  evenScale : Plouffe.Contracts.evenScale
  vepstas : Plouffe.Contracts.vepstas
  kCoefficients : Plouffe.Contracts.kCoefficients
  evenData : Plouffe.Contracts.evenData
  deltaKernel : Plouffe.Contracts.deltaKernel
  deltaOrder : Plouffe.Contracts.deltaOrder
  evenCombinationNegative : Plouffe.Contracts.evenCombinationNegative
  etaLog : Plouffe.Contracts.etaLog
  etaRatio : Plouffe.Contracts.etaRatio
  s1Inversion : Plouffe.Contracts.s1Inversion
  s4Difference : Plouffe.Contracts.s4Difference
  gammaS2 : Plouffe.Contracts.gammaS2
  gammaS4 : Plouffe.Contracts.gammaS4
  gammaReflection : Plouffe.Contracts.gammaReflection
  geometricMajorant : Plouffe.Contracts.geometricMajorant

  lambertParity : Plouffe.Contracts.lambertParity

  vepstasPolynomial : Plouffe.Contracts.vepstasPolynomial

  etaGamma : Plouffe.Contracts.etaGamma

/-- Only the intermediate contracts actually used to derive principal conclusions.
The full Evidence interface remains available for all auxiliary obligations. -/
structure PrincipalEvidence : Prop where
  oddData : Contracts.oddData
  oddCoefficients : Contracts.oddCoefficients
  oddCombinationPositive : Contracts.oddCombinationPositive
  evenData : Contracts.evenData
  evenCombinationNegative : Contracts.evenCombinationNegative
  kCoefficients : Contracts.kCoefficients
  evenScale : Contracts.evenScale
  zetaReal : Contracts.zetaReal
  s1Inversion : Contracts.s1Inversion
  s4Difference : Contracts.s4Difference

/-- Compatibility projection; no principal conclusion is an input field. -/
theorem Evidence.toPrincipalEvidence (h : Evidence) : PrincipalEvidence where
  oddData := h.oddData
  oddCoefficients := h.oddCoefficients
  oddCombinationPositive := h.oddCombinationPositive
  evenData := h.evenData
  evenCombinationNegative := h.evenCombinationNegative
  kCoefficients := h.kCoefficients
  evenScale := h.evenScale
  zetaReal := h.zetaReal
  s1Inversion := h.s1Inversion
  s4Difference := h.s4Difference

/-- All advertised principal conclusions. Not an input to the reduction. -/
structure Principal : Prop where
  oddPi : Specification.oddPi
  oddZeta : Specification.oddZeta
  evenPi : Specification.evenPi
  evenZeta : Specification.evenZeta
  piBase : Specification.piBase
  denominatorSigns : Specification.denominatorSigns

namespace Reduction
/-- Admission-free reduction: analytic and intermediate obligations are explicit parameters. -/
theorem principalCore (h : PrincipalEvidence) : Principal := by
  have odd : ∀ m : ℕ, 1 ≤ m →
      0 < (D m:ℝ) ∧
      Real.pi^(4*m-1) = (4:ℝ)^(2*m-1)/(D m:ℝ)*S (4*m-1) 1-
        ((4:ℝ)^(2*m-1)+1)/(D m:ℝ)*S (4*m-1) 2+1/(D m:ℝ)*S (4*m-1) 4 ∧
      (riemannZeta ((4*m-1:ℕ):ℂ)).re =
        -(F (2*m-1):ℝ)*(4:ℝ)^(4*m-2)/(D m:ℝ)*S (4*m-1) 1+
        (G (2*m-1):ℝ)*(4:ℝ)^(2*m-1)/(D m:ℝ)*S (4*m-1) 2-
        (F (2*m-1):ℝ)*(4:ℝ)^(2*m-1)/(D m:ℝ)*S (4*m-1) 4 := by
    intro m hm
    obtain ⟨hc,hu⟩ := h.oddData m hm
    obtain ⟨hq,hpow,hdef⟩ := h.oddCoefficients m hm
    have hprod : 0 < (D m:ℝ)*Real.pi^(4*m-1) := by
      rw [hu]
      exact h.oddCombinationPositive _ _ hq
    have hd : 0 < (D m:ℝ) := by nlinarith [pow_pos Real.pi_pos (4*m-1)]
    have sol := Algebra.odd_solve ((4:ℝ)^(2*m-1)) (F (2*m-1):ℝ) (G (2*m-1):ℝ)
      (D m:ℝ) (S (4*m-1) 1) (S (4*m-1) 2) (S (4*m-1) 4)
      (Real.pi^(4*m-1)) ((riemannZeta ((4*m-1:ℕ):ℂ)).re) (ne_of_gt hd) hdef hc hu
    exact ⟨hd,sol.1,by simpa only [hpow] using sol.2⟩
  have even : ∀ m : ℕ, 1 ≤ m →
      (E m:ℝ) < 0 ∧
      Real.pi^(4*m+1) = -(4:ℝ)^(2*m)/(E m:ℝ)*S (4*m+1) 1+
        2*(K m:ℝ)*((2:ℝ)^(4*m+1)-(-4:ℝ)^m+1)/(E m:ℝ)*S (4*m+1) 2+
        (1-4*(K m:ℝ))/(E m:ℝ)*S (4*m+1) 4 ∧
      (riemannZeta ((4*m+1:ℕ):ℂ)).re =
        -((16:ℝ)^m*(2*(E m:ℝ)-(16:ℝ)^m*(G (2*m):ℝ)))/
          (((16:ℝ)^m-1)*(E m:ℝ))*S (4*m+1) 1-
        (2*(16:ℝ)^m*(G (2*m):ℝ)*(K m:ℝ)*(2*(16:ℝ)^m-(-4:ℝ)^m+1))/
          (((16:ℝ)^m-1)*(E m:ℝ))*S (4*m+1) 2-
        ((16:ℝ)^m*(G (2*m):ℝ)*(1-4*(K m:ℝ))-2*(E m:ℝ))/
          (((16:ℝ)^m-1)*(E m:ℝ))*S (4*m+1) 4 := by
    intro m hm
    obtain ⟨_,_,hp4,hp2,hp,hq,hk1,hk2⟩ := h.kCoefficients m hm
    have hu := h.evenData m hm
    have hn := h.evenCombinationNegative (4*m+1) ((16:ℝ)^m) ((-4:ℝ)^m) hp hq
    have hprod : (E m:ℝ)*Real.pi^(4*m+1) < 0 := by
      rw [hu,hk1,hk2]
      convert hn using 1; ring
    have he : (E m:ℝ) < 0 := by nlinarith [pow_pos Real.pi_pos (4*m+1)]
    have hpne : (16:ℝ)^m-1 ≠ 0 := by linarith
    have sol := Algebra.even_solve ((16:ℝ)^m) ((-4:ℝ)^m) (G (2*m):ℝ) (K m:ℝ)
      (E m:ℝ) (S (4*m+1) 1) (S (4*m+1) 2) (S (4*m+1) 4)
      (Real.pi^(4*m+1)) ((riemannZeta ((4*m+1:ℕ):ℂ)).re) (ne_of_lt he) hpne hu (h.evenScale m hm)
    exact ⟨he,by simpa only [hp4,hp2] using sol.1,sol.2⟩
  refine ⟨?_,?_,?_,?_,?_,?_⟩
  · intro m hm
    exact (odd m hm).2.1
  · intro m hm
    rw [h.zetaReal (4*m-1) (by omega)]
    exact congrArg (fun x : ℝ => (x:ℂ)) (odd m hm).2.2
  · intro m hm
    exact (even m hm).2.1
  · intro m hm
    rw [h.zetaReal (4*m+1) (by omega)]
    exact congrArg (fun x : ℝ => (x:ℂ)) (even m hm).2.2
  · change Real.pi = 72*S 1 1-96*S 1 2+24*S 1 4
    have hi := h.s1Inversion
    have hd := h.s4Difference
    unfold Contracts.s1Inversion at hi
    unfold Contracts.s4Difference at hd
    linarith
  · intro m hm
    constructor
    · exact_mod_cast (odd m hm).1
    · exact_mod_cast (even m hm).1

/-- Backward-compatible full-evidence reduction with unchanged statement. -/
theorem principal (h : Evidence) : Principal :=
  principalCore h.toPrincipalEvidence

end Reduction
end Plouffe
