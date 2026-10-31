/-
Copyright (c) 2026 Patrick Lopatto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Lopatto
-/
module

public import Plouffe.Contracts
public import Plouffe.Proofs.GammaEndpoints
public import Plouffe.Proofs.Gamma.Evaluation
public import Plouffe.Proofs.Vepstas
public import Plouffe.Proofs.Specializations
public import Plouffe.Proofs.EtaRatio
public import Plouffe.Proofs.Endpoint
public import Plouffe.Proofs.Ramanujan
public import Plouffe.Proofs.EtaLog
public import Plouffe.Proofs.Parity
public import Plouffe.Proofs.Signs
public import Plouffe.Proofs.Double
public import Plouffe.Proofs.Coth
public import Plouffe.Proofs.Zeta
public import Plouffe.Proofs.Series
public import Plouffe.Proofs.Elementary

public section
namespace Plouffe.Obligations

/-- Closed proof node SER-S; independently compiled and axiom-audited. -/
theorem summableS : Plouffe.Contracts.summableS := by
  exact Plouffe.Proofs.Series.summableS

/-- Closed proof node SER-T; independently compiled and axiom-audited. -/
theorem summableT : Plouffe.Contracts.summableT := by
  exact Plouffe.Proofs.Series.summableT

/-- Closed proof node SER-POS; independently compiled and axiom-audited. -/
theorem positive : Plouffe.Contracts.positive := by
  exact Plouffe.Proofs.Series.positive

/-- Closed proof node SER-MONO; independently compiled and axiom-audited. -/
theorem strictParameter : Plouffe.Contracts.strictParameter := by
  exact Plouffe.Proofs.Series.strictParameter

/-- Closed proof node SER-TS; independently compiled and axiom-audited. -/
theorem fermiBose : Plouffe.Contracts.fermiBose := by
  exact Plouffe.Proofs.Series.fermiBose

/-- Closed proof node CAST-L; independently compiled and axiom-audited. -/
theorem lambertReal : Plouffe.Contracts.lambertReal := by
  exact Plouffe.Proofs.Series.lambertReal

/-- Closed proof node SER-L; independently compiled and axiom-audited. -/
theorem summableL : Plouffe.Contracts.summableL := by
  exact Plouffe.Proofs.Series.summableL

/-- Closed proof node CAST-Z; independently compiled and axiom-audited. -/
theorem zetaReal : Plouffe.Contracts.zetaReal := by
  exact Plouffe.Proofs.Zeta.zetaReal

/-- Closed proof node CAST-ZSUM; independently compiled and axiom-audited. -/
theorem zetaPositiveSeries : Plouffe.Contracts.zetaPositiveSeries := by
  exact Plouffe.Proofs.Zeta.zetaPositiveSeries

/-- Closed proof node ALG-PF; independently compiled and axiom-audited. -/
theorem finitePartialFractions : Plouffe.Contracts.finitePartialFractions := by
  exact Plouffe.Proofs.Elementary.finitePartialFractions

/-- Closed proof node ANA-COTH; independently compiled and axiom-audited. -/
theorem cothKernel : Plouffe.Contracts.cothKernel := by
  exact Plouffe.Proofs.Coth.cothKernel

/-- Closed proof node ANA-DOUBLE; independently compiled and axiom-audited. -/
theorem doubleSummable : Plouffe.Contracts.doubleSummable := by
  exact Plouffe.Proofs.Double.doubleSummable

/-- Closed proof node RAM-C; independently compiled and axiom-audited. -/
theorem ramanujanComplex : Plouffe.Contracts.ramanujanComplex := by
  exact Plouffe.Proofs.Ramanujan.ramanujanComplex

/-- Closed proof node RAM-R; independently compiled and axiom-audited. -/
theorem ramanujanReal : Plouffe.Contracts.ramanujanReal := by
  exact Plouffe.Proofs.Specializations.ramanujanReal

/-- Closed proof node RAM-CENTER; independently compiled and axiom-audited. -/
theorem center : Plouffe.Contracts.center := by
  exact Plouffe.Proofs.Specializations.center

/-- Closed proof node EQ-1; independently compiled and axiom-audited. -/
theorem oddCenter : Plouffe.Contracts.oddCenter := by
  exact Plouffe.Proofs.Specializations.oddCenter

/-- Closed proof node ODD-SCALE; independently compiled and axiom-audited. -/
theorem oddScale : Plouffe.Contracts.oddScale := by
  exact Plouffe.Proofs.Specializations.oddScale

/-- Closed proof node ODD-DATA; independently compiled and axiom-audited. -/
theorem oddData : Plouffe.Contracts.oddData := by
  exact Plouffe.Proofs.Specializations.oddData

/-- Closed proof node ODD-KERNEL; independently compiled and axiom-audited. -/
theorem oddKernel : Plouffe.Contracts.oddKernel := by
  exact Plouffe.Proofs.Elementary.oddKernel

/-- Closed proof node ODD-POS; independently compiled and axiom-audited. -/
theorem oddCombinationPositive : Plouffe.Contracts.oddCombinationPositive := by
  exact Plouffe.Proofs.Signs.oddCombinationPositive

/-- Closed proof node COEFF-ODD; independently compiled and axiom-audited. -/
theorem oddCoefficients : Plouffe.Contracts.oddCoefficients := by
  exact Plouffe.Proofs.Elementary.oddCoefficients

/-- Closed proof node EQ-2; independently compiled and axiom-audited. -/
theorem evenScale : Plouffe.Contracts.evenScale := by
  exact Plouffe.Proofs.Specializations.evenScale

/-- Closed proof node VEP; independently compiled and axiom-audited. -/
theorem vepstas : Plouffe.Contracts.vepstas := by
  exact Plouffe.Proofs.Vepstas.vepstas

/-- Closed proof node COEFF-K; independently compiled and axiom-audited. -/
theorem kCoefficients : Plouffe.Contracts.kCoefficients := by
  exact Plouffe.Proofs.Elementary.kCoefficients

/-- Closed proof node EVEN-DATA; independently compiled and axiom-audited. -/
theorem evenData : Plouffe.Contracts.evenData := by
  exact Plouffe.Proofs.Vepstas.evenData

/-- Closed proof node DELTA-KERNEL; independently compiled and axiom-audited. -/
theorem deltaKernel : Plouffe.Contracts.deltaKernel := by
  exact Plouffe.Proofs.Elementary.deltaKernel

/-- Closed proof node DELTA; independently compiled and axiom-audited. -/
theorem deltaOrder : Plouffe.Contracts.deltaOrder := by
  exact Plouffe.Proofs.Signs.deltaOrder

/-- Closed proof node EVEN-NEG; independently compiled and axiom-audited. -/
theorem evenCombinationNegative : Plouffe.Contracts.evenCombinationNegative := by
  exact Plouffe.Proofs.Signs.evenCombinationNegative

/-- Closed proof node ETA-LOG; independently compiled and axiom-audited. -/
theorem etaLog : Plouffe.Contracts.etaLog := by
  exact Plouffe.Proofs.EtaLog.etaLog

/-- Closed proof node ETA-RATIO; independently compiled and axiom-audited. -/
theorem etaRatio : Plouffe.Contracts.etaRatio := by
  exact Plouffe.Proofs.EtaRatio.etaRatio

/-- Closed proof node END-INVERT; independently compiled and axiom-audited. -/
theorem s1Inversion : Plouffe.Contracts.s1Inversion := by
  exact Plouffe.Proofs.Endpoint.s1Inversion

/-- Closed proof node END-DIFF; independently compiled and axiom-audited. -/
theorem s4Difference : Plouffe.Contracts.s4Difference := by
  exact Plouffe.Proofs.Endpoint.s4Difference

/-- Closed proof node GAMMA-S2; independently compiled and axiom-audited. -/
theorem gammaS2 : Plouffe.Contracts.gammaS2 := by
  exact Plouffe.Proofs.GammaEndpoints.gammaS2

/-- Closed proof node GAMMA-S4; independently compiled and axiom-audited. -/
theorem gammaS4 : Plouffe.Contracts.gammaS4 := by
  exact Plouffe.Proofs.GammaEndpoints.gammaS4

/-- Closed proof node GAMMA-REFL; independently compiled and axiom-audited. -/
theorem gammaReflection : Plouffe.Contracts.gammaReflection := by
  exact Plouffe.Proofs.Elementary.gammaReflection

/-- Closed proof node SER-BOUND; independently compiled and axiom-audited. -/
theorem geometricMajorant : Plouffe.Contracts.geometricMajorant := by
  exact Plouffe.Proofs.Series.geometricMajorant

/-- Closed proof node VEP-PARITY; independently compiled and axiom-audited. -/
theorem lambertParity : Plouffe.Contracts.lambertParity := by
  exact Plouffe.Proofs.Parity.lambertParity

/-- Closed proof node VEP-POLY; independently compiled and axiom-audited. -/
theorem vepstasPolynomial : Plouffe.Contracts.vepstasPolynomial := by
  exact Plouffe.Proofs.Vepstas.vepstasPolynomial

/-- Closed proof node ETA-GAMMA; independently compiled and axiom-audited. -/
theorem etaGamma : Plouffe.Contracts.etaGamma := by
  exact Plouffe.Proofs.Gamma.etaGamma

end Plouffe.Obligations
