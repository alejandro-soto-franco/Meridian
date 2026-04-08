/-
Copyright 2026 Alejandro Jose Soto Franco. Licensed under Apache 2.0.
-/
import Lean

/-!
# Theorem Extraction

Split the current file into individual declarations with metadata: name, signature,
proof (or sorry), docstring, local and external dependency lists, tactic count,
proof term size.

## Commands

- `#extract_theorems`: output `List TheoremInfo`
-/

namespace Meridian.Core.TheoremExtract

open Lean Elab Command Meta

end Meridian.Core.TheoremExtract
