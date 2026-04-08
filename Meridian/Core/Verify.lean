/-
Copyright 2026 Alejandro Jose Soto Franco. Licensed under Apache 2.0.
-/
import Lean

/-!
# Proof Verification

Given a declaration name with `sorry` and a candidate proof term, check if it
type-checks against the expected type. Wrapper around `Lean.Elab.Term.elabTerm`.

## Commands

- `#verify_proof declName`: verify a candidate proof against a sorry's type
-/

namespace Meridian.Core.Verify

open Lean Elab Command Meta

end Meridian.Core.Verify
