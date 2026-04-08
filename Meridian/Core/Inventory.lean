/-
Copyright 2026 Alejandro Jose Soto Franco. Licensed under Apache 2.0.
-/
import Lean

/-!
# Sorry Inventory

Produce a table of all sorries in the project: file, declaration name, goal type,
and estimated category (A/B/C based on Mathlib reachability).

## Commands

- `#sorry_inventory`: tabular sorry report with auto-categorisation
-/

namespace Meridian.Core.Inventory

open Lean Elab Command Meta

end Meridian.Core.Inventory
