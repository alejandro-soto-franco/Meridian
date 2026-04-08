/-
Copyright 2026 Alejandro Jose Soto Franco. Licensed under Apache 2.0.
-/
import Lean

/-!
# Dependency Graph

Build a directed graph of declaration dependencies. Edges: `A -> B` means `A` uses
`B` in its proof or type. Annotates each node with sorry count, proven/sorry status,
and which Mathlib modules it touches.

## Commands

- `#dep_graph`: output structured `DepGraph` + DOT format for Graphviz
-/

namespace Meridian.Core.DepGraph

open Lean Elab Command Meta

end Meridian.Core.DepGraph
