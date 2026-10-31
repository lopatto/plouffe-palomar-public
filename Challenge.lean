/-
Copyright (c) 2026 Patrick Lopatto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Lopatto
-/
module

public import Mathlib.NumberTheory.Bernoulli
public import Mathlib.NumberTheory.LSeries.RiemannZeta

/-!
# Literal mathematical definitions

The series use the positive integers through successor indexing.
The coefficient sums live in ℚ; analytic statements cast them explicitly.
No convergence theorem or paper identity is asserted by these definitions.
-/

@[expose] public section

namespace Plouffe

/-- The manuscript's Bose-denominator series, with k = j+1. -/
noncomputable def S (s : ℕ) (r : ℝ) : ℝ :=
  ∑' j : ℕ, 1 / (((j + 1 : ℕ) : ℝ) ^ s *
    (Real.exp (Real.pi * r * ((j + 1 : ℕ) : ℝ)) - 1))

/-- The manuscript's Fermi-denominator series, with k = j+1. -/
noncomputable def T (s : ℕ) (r : ℝ) : ℝ :=
  ∑' j : ℕ, 1 / (((j + 1 : ℕ) : ℝ) ^ s *
    (Real.exp (Real.pi * r * ((j + 1 : ℕ) : ℝ)) + 1))

/-- Alternating even-index Bernoulli convolution, k = 0,...,n+1. -/
def F (n : ℕ) : ℚ :=
  ∑ k ∈ Finset.range (n + 2),
    (-1 : ℚ) ^ k * bernoulli (2 * k) * bernoulli (2 * n + 2 - 2 * k) /
      ((Nat.factorial (2 * k) : ℚ) * (Nat.factorial (2 * n + 2 - 2 * k) : ℚ))

/-- The same convolution with weight (-4)^k. -/
def G (n : ℕ) : ℚ :=
  ∑ k ∈ Finset.range (n + 2),
    (-4 : ℚ) ^ k * bernoulli (2 * k) * bernoulli (2 * n + 2 - 2 * k) /
      ((Nat.factorial (2 * k) : ℚ) * (Nat.factorial (2 * n + 2 - 2 * k) : ℚ))

/-- The manuscript's 4k-index Bernoulli convolution, k = 0,...,n. -/
def H (n : ℕ) : ℚ :=
  ∑ k ∈ Finset.range (n + 1),
    (-4 : ℚ) ^ (n + k) * bernoulli (4 * k) * bernoulli (4 * n + 2 - 4 * k) /
      ((Nat.factorial (4 * k) : ℚ) * (Nat.factorial (4 * n + 2 - 4 * k) : ℚ))

/-- Rational denominator for the 4m-1 family; nonvanishing is claimed only for m≥1. -/
def D (m : ℕ) : ℚ :=
  (4 : ℚ) ^ (2 * m - 1) *
    (((4 : ℚ) ^ (2 * m - 1) + 1) * F (2 * m - 1) - G (2 * m - 1)) / 2

/-- Rational elimination coefficient for the 4m+1 family, used only for m≥1. -/
def K (m : ℕ) : ℚ :=
  ((1 - (4 : ℚ) ^ (2 * m)) / 2) /
    (1 + (-4 : ℚ) ^ m - (2 : ℚ) ^ (4 * m + 1))

/-- Rational denominator for the 4m+1 family; nonvanishing is claimed only for m≥1. -/
def E (m : ℕ) : ℚ :=
  (4 : ℚ) ^ (2 * m) / 2 * G (2 * m) -
    (2 : ℚ) ^ (4 * m + 1) * K m * H m -
    (2 : ℚ) ^ (4 * m) * K m * G (2 * m)

end Plouffe

public section
namespace Plouffe.Results

/-- Advertised principal result; deliberate independent Challenge hole. -/
theorem oddPi :
∀ m : ℕ, 1 ≤ m →
    Real.pi ^ (4 * m - 1) =
      (4 : ℝ) ^ (2 * m - 1) / (D m : ℝ) * S (4 * m - 1) 1 -
      ((4 : ℝ) ^ (2 * m - 1) + 1) / (D m : ℝ) * S (4 * m - 1) 2 +
      1 / (D m : ℝ) * S (4 * m - 1) 4 := by
  sorry

/-- Advertised principal result; deliberate independent Challenge hole. -/
theorem oddZeta :
∀ m : ℕ, 1 ≤ m →
    riemannZeta ((4 * m - 1 : ℕ) : ℂ) =
      (((-(F (2 * m - 1) : ℝ) * (4 : ℝ) ^ (4 * m - 2) / (D m : ℝ) *
            S (4 * m - 1) 1 +
          (G (2 * m - 1) : ℝ) * (4 : ℝ) ^ (2 * m - 1) / (D m : ℝ) *
            S (4 * m - 1) 2 -
          (F (2 * m - 1) : ℝ) * (4 : ℝ) ^ (2 * m - 1) / (D m : ℝ) *
            S (4 * m - 1) 4) : ℝ) : ℂ) := by
  sorry

/-- Advertised principal result; deliberate independent Challenge hole. -/
theorem evenPi :
∀ m : ℕ, 1 ≤ m →
    Real.pi ^ (4 * m + 1) =
      -((4 : ℝ) ^ (2 * m)) / (E m : ℝ) * S (4 * m + 1) 1 +
      2 * (K m : ℝ) * ((2 : ℝ) ^ (4 * m + 1) - (-4 : ℝ) ^ m + 1) /
        (E m : ℝ) * S (4 * m + 1) 2 +
      (1 - 4 * (K m : ℝ)) / (E m : ℝ) * S (4 * m + 1) 4 := by
  sorry

/-- Advertised principal result; deliberate independent Challenge hole. -/
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
      ) : ℝ) : ℂ) := by
  sorry

/-- Advertised principal result; deliberate independent Challenge hole. -/
theorem piBase :
Real.pi = 72 * S 1 1 - 96 * S 1 2 + 24 * S 1 4 := by
  sorry

/-- Advertised principal result; deliberate independent Challenge hole. -/
theorem denominatorSigns :
∀ m : ℕ, 1 ≤ m → 0 < D m ∧ E m < 0 := by
  sorry

end Plouffe.Results
