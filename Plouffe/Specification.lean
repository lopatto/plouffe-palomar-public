/-
Copyright (c) 2026 Patrick Lopatto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Lopatto
-/
module

public import Plouffe.Definitions

/-!
# Principal proposition specifications

Each declaration below is a proposition-valued definition. Defining a proposition
does not prove it. The proofs are supplied separately by `Plouffe.principalResults`
and the identically named exports in `Solution.lean`. The independent Challenge
exposes these equations directly, with the small supporting definitions inlined.
-/

@[expose] public section

namespace Plouffe.Specification

/-- Principal target: the 4m-1 formula for powers of π. Proved by the corresponding Solution export. -/
def oddPi : Prop :=
  ∀ m : ℕ, 1 ≤ m →
    Real.pi ^ (4 * m - 1) =
      (4 : ℝ) ^ (2 * m - 1) / (D m : ℝ) * S (4 * m - 1) 1 -
      ((4 : ℝ) ^ (2 * m - 1) + 1) / (D m : ℝ) * S (4 * m - 1) 2 +
      1 / (D m : ℝ) * S (4 * m - 1) 4

/-- Principal target: the 4m-1 odd-zeta formula, stated for native complex zeta. Proved by the corresponding Solution export. -/
def oddZeta : Prop :=
  ∀ m : ℕ, 1 ≤ m →
    riemannZeta ((4 * m - 1 : ℕ) : ℂ) =
      (((-(F (2 * m - 1) : ℝ) * (4 : ℝ) ^ (4 * m - 2) / (D m : ℝ) *
            S (4 * m - 1) 1 +
          (G (2 * m - 1) : ℝ) * (4 : ℝ) ^ (2 * m - 1) / (D m : ℝ) *
            S (4 * m - 1) 2 -
          (F (2 * m - 1) : ℝ) * (4 : ℝ) ^ (2 * m - 1) / (D m : ℝ) *
            S (4 * m - 1) 4) : ℝ) : ℂ)

/-- Principal target: the 4m+1 formula for powers of π, with m≥1. Proved by the corresponding Solution export. -/
def evenPi : Prop :=
  ∀ m : ℕ, 1 ≤ m →
    Real.pi ^ (4 * m + 1) =
      -((4 : ℝ) ^ (2 * m)) / (E m : ℝ) * S (4 * m + 1) 1 +
      2 * (K m : ℝ) * ((2 : ℝ) ^ (4 * m + 1) - (-4 : ℝ) ^ m + 1) /
        (E m : ℝ) * S (4 * m + 1) 2 +
      (1 - 4 * (K m : ℝ)) / (E m : ℝ) * S (4 * m + 1) 4

/-- Principal target: the 4m+1 odd-zeta formula, with m≥1. Proved by the corresponding Solution export. -/
def evenZeta : Prop :=
  ∀ m : ℕ, 1 ≤ m →
    riemannZeta ((4 * m + 1 : ℕ) : ℂ) =
      (((
        -((16 : ℝ) ^ m * (2 * (E m : ℝ) - (16 : ℝ) ^ m * (G (2 * m) : ℝ))) /
          (((16 : ℝ) ^ m - 1) * (E m : ℝ)) * S (4 * m + 1) 1 -
        (2 * (16 : ℝ) ^ m * (G (2 * m) : ℝ) * (K m : ℝ) *
          (2 * (16 : ℝ) ^ m - (-4 : ℝ) ^ m + 1)) /
          (((16 : ℝ) ^ m - 1) * (E m : ℝ)) * S (4 * m + 1) 2 -
        ((16 : ℝ) ^ m * (G (2 * m) : ℝ) * (1 - 4 * (K m : ℝ)) -
          2 * (E m : ℝ)) /
          (((16 : ℝ) ^ m - 1) * (E m : ℝ)) * S (4 * m + 1) 4
      ) : ℝ) : ℂ)

/-- Separate endpoint: the introductory formula for π. Proved by the corresponding Solution export. -/
def piBase : Prop :=
  Real.pi = 72 * S 1 1 - 96 * S 1 2 + 24 * S 1 4

/-- Nonvanishing results in their original rational coefficient field. Proved by the corresponding Solution export. -/
def denominatorSigns : Prop :=
  ∀ m : ℕ, 1 ≤ m → 0 < D m ∧ E m < 0

end Plouffe.Specification
