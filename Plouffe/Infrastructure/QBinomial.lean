/-
Copyright (c) 2026 Patrick Lopatto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Lopatto
-/
module

public import Mathlib.Basic.Real.Basic
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Data.Nat.Choose.Basic

@[expose] public section
namespace Plouffe.QBinomial

/-- Finite Euler product, with positive successor indexing. -/
noncomputable def poch (Q : ℝ) (n : ℕ) : ℝ :=
  ∏ j ∈ Finset.range n, (1 - Q^(j+1))

/-- Gaussian quotient used under the explicit domain 0 < Q < 1. -/
noncomputable def gaussian (Q : ℝ) (n k : ℕ) : ℝ :=
  if k ≤ n then poch Q n / (poch Q k * poch Q (n-k)) else 0

/-- Triangularly weighted finite Gaussian coefficient. -/
noncomputable def coefficient (Q : ℝ) (n k : ℕ) : ℝ :=
  Q^(Nat.choose k 2) * gaussian Q n k

theorem poch_eq_prod (Q : ℝ) (n : ℕ) :
    poch Q n = ∏ j ∈ Finset.range n, (1 - Q^(j+1)) := rfl

theorem gaussian_eq_quotient (Q : ℝ) (n k : ℕ) :
    gaussian Q n k = if k ≤ n then poch Q n / (poch Q k * poch Q (n-k)) else 0 := rfl

theorem coefficient_eq_weight (Q : ℝ) (n k : ℕ) :
    coefficient Q n k = Q^(Nat.choose k 2) * gaussian Q n k := rfl

end Plouffe.QBinomial
