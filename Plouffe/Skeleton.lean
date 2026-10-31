/-
Copyright (c) 2026 Patrick Lopatto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Lopatto
-/
module

public import Plouffe.Obligations
public import Plouffe.Reduction

public section
namespace Plouffe
/-- Complete proof of every original intermediate contract; compatibility name retained. -/
theorem pendingEvidence : Evidence where
  summableS := Obligations.summableS
  summableT := Obligations.summableT
  positive := Obligations.positive
  strictParameter := Obligations.strictParameter
  fermiBose := Obligations.fermiBose
  lambertReal := Obligations.lambertReal
  summableL := Obligations.summableL
  zetaReal := Obligations.zetaReal
  zetaPositiveSeries := Obligations.zetaPositiveSeries
  finitePartialFractions := Obligations.finitePartialFractions
  cothKernel := Obligations.cothKernel
  doubleSummable := Obligations.doubleSummable
  ramanujanComplex := Obligations.ramanujanComplex
  ramanujanReal := Obligations.ramanujanReal
  center := Obligations.center
  oddCenter := Obligations.oddCenter
  oddScale := Obligations.oddScale
  oddData := Obligations.oddData
  oddKernel := Obligations.oddKernel
  oddCombinationPositive := Obligations.oddCombinationPositive
  oddCoefficients := Obligations.oddCoefficients
  evenScale := Obligations.evenScale
  vepstas := Obligations.vepstas
  kCoefficients := Obligations.kCoefficients
  evenData := Obligations.evenData
  deltaKernel := Obligations.deltaKernel
  deltaOrder := Obligations.deltaOrder
  evenCombinationNegative := Obligations.evenCombinationNegative
  etaLog := Obligations.etaLog
  etaRatio := Obligations.etaRatio
  s1Inversion := Obligations.s1Inversion
  s4Difference := Obligations.s4Difference
  gammaS2 := Obligations.gammaS2
  gammaS4 := Obligations.gammaS4
  gammaReflection := Obligations.gammaReflection
  geometricMajorant := Obligations.geometricMajorant
  lambertParity := Obligations.lambertParity
  vepstasPolynomial := Obligations.vepstasPolynomial
  etaGamma := Obligations.etaGamma

/-- Principal proof inputs use only closed intermediate nodes, independently of Gamma auxiliaries. -/
theorem principalEvidence : PrincipalEvidence where
  oddData := Obligations.oddData
  oddCoefficients := Obligations.oddCoefficients
  oddCombinationPositive := Obligations.oddCombinationPositive
  evenData := Obligations.evenData
  evenCombinationNegative := Obligations.evenCombinationNegative
  kCoefficients := Obligations.kCoefficients
  evenScale := Obligations.evenScale
  zetaReal := Obligations.zetaReal
  s1Inversion := Obligations.s1Inversion
  s4Difference := Obligations.s4Difference

/-- All advertised principal conclusions, with no unresolved proof input. -/
theorem principalResults : Principal := Reduction.principalCore principalEvidence

/-- Compatibility alias; principalResults is the unconditional proved package. -/
theorem pendingPrincipal : Principal := principalResults
end Plouffe
