/-
Copyright (c) 2026 Patrick Lopatto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Lopatto
-/
module

public import Plouffe.Skeleton
public import Plouffe.Examples

public section
namespace Plouffe.Corollaries

/-- Unconditional numerical identity from the proved principal families. -/
theorem pi3 : Real.pi^3 = 720*S 3 1-900*S 3 2+180*S 3 4 := Examples.pi3 principalResults

/-- Unconditional numerical identity from the proved principal families. -/
theorem pi5 : Real.pi^5 = 7056*S 5 1-6993*S 5 2-63*S 5 4 := Examples.pi5 principalResults

/-- Unconditional numerical identity from the proved principal families. -/
theorem pi7 : Real.pi^7 = (907200/13:ℝ)*S 7 1-70875*S 7 2+(14175/13:ℝ)*S 7 4 := Examples.pi7 principalResults

/-- Unconditional numerical identity from the proved principal families. -/
theorem zeta3 : riemannZeta (3:ℂ) = ((28*S 3 1-37*S 3 2+7*S 3 4:ℝ):ℂ) := Examples.zeta3 principalResults

/-- Unconditional numerical identity from the proved principal families. -/
theorem zeta5 : riemannZeta (5:ℂ) = ((24*S 5 1-(259/10:ℝ)*S 5 2-(1/10:ℝ)*S 5 4:ℝ):ℂ) := Examples.zeta5 principalResults

/-- Unconditional numerical identity from the proved principal families. -/
theorem zeta7 : riemannZeta (7:ℂ) = (((304/13:ℝ)*S 7 1-(103/4:ℝ)*S 7 2+(19/52:ℝ)*S 7 4:ℝ):ℂ) := Examples.zeta7 principalResults

end Plouffe.Corollaries
