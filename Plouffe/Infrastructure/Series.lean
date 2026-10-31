/-
Copyright (c) 2026 Patrick Lopatto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Lopatto
-/
module

public import Plouffe.Definitions
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum

@[expose] public section
namespace Plouffe

/-- The literal complex Lambert `tsum` with positive successor indices and weight exponent `2*n+1`. -/
noncomputable def L (n : ℕ) (a : ℂ) : ℂ :=
  ∑' j : ℕ, 1 / (((j+1:ℕ):ℂ)^(2*n+1)*(Complex.exp (2*a*((j+1:ℕ):ℂ))-1))

namespace Contracts

/-- SER-S: §1 S definition. Statement only. -/
def summableS : Prop :=
  ∀ (s : ℕ) (r : ℝ), 0 < r → Summable (fun j : ℕ => 1 / (((j+1:ℕ):ℝ)^s * (Real.exp (Real.pi*r*((j+1:ℕ):ℝ))-1)))

/-- SER-T: §2 T definition. Statement only. -/
def summableT : Prop :=
  ∀ (s : ℕ) (r : ℝ), 0 < r → Summable (fun j : ℕ => 1 / (((j+1:ℕ):ℝ)^s * (Real.exp (Real.pi*r*((j+1:ℕ):ℝ))+1)))

/-- SER-POS: §2 denominator arguments. Statement only. -/
def positive : Prop :=
  ∀ (s : ℕ) (r : ℝ), 0 < r → 0 < S s r ∧ 0 < T s r

/-- SER-MONO: §2 positive differences. Statement only. -/
def strictParameter : Prop :=
  ∀ (s : ℕ) (r t : ℝ), 0 < r → r < t → S s t < S s r

/-- SER-TS: §2 T/S identity. Statement only. -/
def fermiBose : Prop :=
  ∀ (s : ℕ) (r : ℝ), 0 < r → T s r = S s r - 2*S s (2*r)

/-- CAST-L: Theorem 1 real/complex adapter. Statement only. -/
def lambertReal : Prop :=
  ∀ (n : ℕ) (a : ℝ), 0 < a → L n (a:ℂ) = ((S (2*n+1) (2*a/Real.pi):ℝ):ℂ)

/-- SER-L: Theorem 1 prerequisite. Statement only. -/
def summableL : Prop :=
  ∀ (n : ℕ) (a : ℂ), 0 < a.re → Summable (fun j : ℕ => 1 / (((j+1:ℕ):ℂ)^(2*n+1) * (Complex.exp (2*a*((j+1:ℕ):ℂ))-1)))

/-- CAST-Z: Native zeta adapter. Statement only. -/
def zetaReal : Prop :=
  ∀ s : ℕ, 2 ≤ s → riemannZeta (s:ℂ) = (((riemannZeta (s:ℂ)).re:ℝ):ℂ)

/-- CAST-ZSUM: Native zeta adapter. Statement only. -/
def zetaPositiveSeries : Prop :=
  ∀ s : ℕ, 2 ≤ s → Summable (fun j : ℕ => 1 / ((j+1:ℕ):ℂ)^s) ∧ riemannZeta (s:ℂ) = ∑' j : ℕ, 1 / ((j+1:ℕ):ℂ)^s

/-- ALG-PF: Theorem 1 finite algebra. Statement only. -/
def finitePartialFractions : Prop :=
  ∀ (n : ℕ) (X Y : ℂ), 1 ≤ n → X ≠ 0 → Y ≠ 0 → X+Y ≠ 0 → ((X^n)⁻¹ - (-1:ℂ)^n*(Y^n)⁻¹)/(X+Y) = ∑ j ∈ Finset.range n, (-1:ℂ)^j*(X^(n-j))⁻¹*(Y^(j+1))⁻¹

/-- ANA-COTH: Theorem 1 analytic prerequisite. Statement only. -/
def cothKernel : Prop :=
  ∀ a : ℂ, 0 < a.re → (Complex.exp (2*a)+1)/(Complex.exp (2*a)-1)-1/a = ∑' j : ℕ, 2*a/(a^2+(Real.pi:ℂ)^2*((j+1:ℕ):ℂ)^2)

/-- ANA-DOUBLE: Theorem 1 analytic prerequisite. Statement only. -/
def doubleSummable : Prop :=
  ∀ (n : ℕ) (a b : ℂ), 1 ≤ n → 0 < a.re → 0 < b.re → Summable (fun kl : ℕ × ℕ => 1 / (((kl.1+1:ℕ):ℂ)^(2*n) * (a*((kl.1+1:ℕ):ℂ)^2+b*((kl.2+1:ℕ):ℂ)^2)))

/-- ODD-KERNEL: §2 D positive kernel. Statement only. -/
def oddKernel : Prop :=
  ∀ (q t : ℝ), 4 ≤ q → 1 < t → q/(t-1)-(q+1)/(t^2-1)+1/(t^4-1) = t*(q*t^2-t+q)/(t^4-1) ∧ 0 < t*(q*t^2-t+q)/(t^4-1)

/-- DELTA-KERNEL: §2 difference ratio. Statement only. -/
def deltaKernel : Prop :=
  ∀ t : ℝ, 1 < t → (1/(t-1)-1/(t^2-1))/(1/(t^2-1)-1/(t^4-1)) = t+t⁻¹ ∧ 2 < t+t⁻¹

/-- SER-BOUND: Abstract rapidly convergent series. Statement only. -/
def geometricMajorant : Prop :=
  ∀ (s : ℕ) (r : ℝ), 0 < r → ∃ C : ℝ, 0 < C ∧ ∀ j : ℕ, |1 / (((j+1:ℕ):ℝ)^s*(Real.exp (Real.pi*r*((j+1:ℕ):ℝ))-1))| ≤ C*Real.exp (-Real.pi*r)^j

end Contracts
end Plouffe
