/-
Copyright 2026 Alejandro Jose Soto Franco. Licensed under Apache 2.0.
-/
import Lean

/-!
# Counterexample Search

Attempt to find a counterexample for a declaration using Plausible (property-based
testing). Sanity check before spending hours on a sorry that is actually false.

## Commands

- `#disprove declName`: search for counterexamples
-/

namespace Meridian.Core.Disprove

open Lean Elab Command Meta

end Meridian.Core.Disprove
