/-
Copyright 2026 Alejandro Jose Soto Franco. Licensed under Apache 2.0.
-/
import Lean

/-!
# Sorry Extraction

Walk the environment, find all declarations containing `sorry`, and for each one
elaborate the goal type at the sorry site into a standalone lemma stub with fully
resolved universe variables and instance arguments.

## Commands

- `#sorry_extract`: emit standalone `lemma foo.sorried : <type> := sorry` for each sorry
-/

namespace Meridian.Core.SorryExtract

open Lean Elab Command Meta

end Meridian.Core.SorryExtract
