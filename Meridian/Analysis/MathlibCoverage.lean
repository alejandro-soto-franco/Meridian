/-
Copyright 2026 Alejandro Jose Soto Franco. Licensed under Apache 2.0.
-/
import Lean

/-!
# Mathlib Coverage Analysis

Given a goal, find "close" Mathlib lemmas by querying the `DiscrTree` with up to N
mismatches. Classify each near-miss: specialisation gap, exponent gap, dimensionality
gap, or missing infrastructure.

## Commands

- `#mathlib_coverage declName`: find near-miss Mathlib lemmas for a sorry

## Tactics

- `meridian_coverage`: print coverage results in the infoview
-/

namespace Meridian.Analysis.MathlibCoverage

open Lean Elab Command Meta

end Meridian.Analysis.MathlibCoverage
