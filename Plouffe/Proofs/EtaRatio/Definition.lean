/-
Copyright (c) 2026 Patrick Lopatto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Lopatto
-/
module

public import Plouffe.Proofs.EtaRatio.Euler

public section
namespace Plouffe.Proofs.EtaRatio

/-- Frozen literal meaning of the auxiliary Euler product. -/
theorem euler_eq_tprod (q : ℝ) : euler q = ∏' j : ℕ, (1-q^(j+1)) := rfl

end Plouffe.Proofs.EtaRatio
