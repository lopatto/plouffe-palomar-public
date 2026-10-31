/-
Copyright (c) 2026 Patrick Lopatto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Lopatto
-/
module

public import Plouffe.Skeleton

public section
namespace Plouffe.Results

theorem oddPi :
∀ m : ℕ, 1 ≤ m →
    Real.pi ^ (4 * m - 1) =
      (4 : ℝ) ^ (2 * m - 1) / (D m : ℝ) * S (4 * m - 1) 1 -
      ((4 : ℝ) ^ (2 * m - 1) + 1) / (D m : ℝ) * S (4 * m - 1) 2 +
      1 / (D m : ℝ) * S (4 * m - 1) 4 :=
  principalResults.oddPi

theorem oddZeta :
∀ m : ℕ, 1 ≤ m →
    riemannZeta ((4 * m - 1 : ℕ) : ℂ) =
      (((-(F (2 * m - 1) : ℝ) * (4 : ℝ) ^ (4 * m - 2) / (D m : ℝ) *
            S (4 * m - 1) 1 +
          (G (2 * m - 1) : ℝ) * (4 : ℝ) ^ (2 * m - 1) / (D m : ℝ) *
            S (4 * m - 1) 2 -
          (F (2 * m - 1) : ℝ) * (4 : ℝ) ^ (2 * m - 1) / (D m : ℝ) *
            S (4 * m - 1) 4) : ℝ) : ℂ) :=
  principalResults.oddZeta

theorem evenPi :
∀ m : ℕ, 1 ≤ m →
    Real.pi ^ (4 * m + 1) =
      -((4 : ℝ) ^ (2 * m)) / (E m : ℝ) * S (4 * m + 1) 1 +
      2 * (K m : ℝ) * ((2 : ℝ) ^ (4 * m + 1) - (-4 : ℝ) ^ m + 1) /
        (E m : ℝ) * S (4 * m + 1) 2 +
      (1 - 4 * (K m : ℝ)) / (E m : ℝ) * S (4 * m + 1) 4 :=
  principalResults.evenPi

theorem evenZeta :
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
      ) : ℝ) : ℂ) :=
  principalResults.evenZeta

theorem piBase :
Real.pi = 72 * S 1 1 - 96 * S 1 2 + 24 * S 1 4 :=
  principalResults.piBase

theorem denominatorSigns :
∀ m : ℕ, 1 ≤ m → 0 < D m ∧ E m < 0 :=
  principalResults.denominatorSigns

end Plouffe.Results
