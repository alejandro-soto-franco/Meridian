/-
Copyright 2026 Alejandro Jose Soto Franco. Licensed under Apache 2.0.
-/
import Lean

/-!
# Distributional Derivative Tactic

Automate goals involving weak/distributional derivatives and test function
formulations. Handles integration-by-parts reductions, passage between
`HasWeakDerivative` and `HasFDerivAt`, and the "test against all test functions"
pattern.

## Tactics

- `meridian_distrib`: reduce distributional goals to pointwise identities
-/

namespace Meridian.Domain.PDE.Distributional

open Lean Elab Tactic Meta

end Meridian.Domain.PDE.Distributional
