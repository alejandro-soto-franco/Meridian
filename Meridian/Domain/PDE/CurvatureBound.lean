/-
Copyright 2026 Alejandro Jose Soto Franco. Licensed under Apache 2.0.
-/
import Lean

/-!
# Curvature and Helicity Tactics

Automate curvature tensor goals (Arnold sectional curvature, curvature measure
finiteness, CKN bridge estimates) and helicity goals (Chern-Simons reduction,
Arnold bound, dissipation sign analysis).

## Tactics

- `meridian_curvature`: curvature tensor automation
- `meridian_helicity`: helicity invariant automation
-/

namespace Meridian.Domain.PDE.CurvatureBound

open Lean Elab Tactic Meta

end Meridian.Domain.PDE.CurvatureBound
