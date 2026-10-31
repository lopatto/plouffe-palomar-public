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
