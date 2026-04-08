/-
Copyright 2026 Alejandro Jose Soto Franco. Licensed under Apache 2.0.
-/
import Meridian.Analysis.MathlibCoverage
import Meridian.Core.DepGraph

/-!
# Gap Report

Aggregate `MathlibCoverage` across all sorries in the project. Group by missing
infrastructure, rank by `(downstream impact) * (Mathlib closeness)`, output
structured report + Markdown.

## Commands

- `#gap_report`: project-level Mathlib gap analysis
-/

namespace Meridian.Analysis.GapReport

open Lean Elab Command Meta

end Meridian.Analysis.GapReport
