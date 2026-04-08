/-
Copyright 2026 Alejandro Jose Soto Franco. Licensed under Apache 2.0.
-/
import Lean

/-!
# Instance Synthesis Debugging

Hook into `Meta.synthInstance?` to capture the `SynthInstance.State` on failure,
build a structured search tree, and diagnose the failure with actionable suggestions.

## Commands

- `#instance_debug <type>`: diagnose type-class synthesis failure
-/

namespace Meridian.Search.InstanceDebug

open Lean Elab Command Meta

end Meridian.Search.InstanceDebug
