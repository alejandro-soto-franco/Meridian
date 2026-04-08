/-
Copyright 2026 Alejandro Jose Soto Franco. Licensed under Apache 2.0.
-/
import Lean

/-!
# Structural Transforms

Environment-level transformations on declarations.

## Commands

- `#theorem2sorry`: strip all proofs, replace with `sorry`
- `#normalize`: pretty-print all declarations in standard Mathlib format
- `#rename oldName newName`: rename a declaration and all references
-/

namespace Meridian.Core.Transform

open Lean Elab Command Meta

end Meridian.Core.Transform
