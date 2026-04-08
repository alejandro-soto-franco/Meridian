# Meridian

Open-source Lean 4 metaprogramming toolkit for mathematical formalisation. Proof search, sorry extraction, dependency analysis, Mathlib coverage reports, and domain-specific PDE tactics. Runs locally, no network calls, no data leaves your machine.

## Installation

Add to your `lakefile.toml`:

```toml
[[require]]
name = "Meridian"
git = "https://github.com/alejandro-soto-franco/Meridian"
rev = "main"
```

Then `lake update && lake build`.

## Modules

| Import | What you get |
|--------|-------------|
| `import Meridian.Core` | AXLE-equivalent tools: sorry extraction, dependency graph, theorem extraction, verify, structural transforms, counterexample search |
| `import Meridian.Search` | Tactic suggestion, IDA* proof search, goal decomposition, type-class instance debugging |
| `import Meridian.Analysis` | Mathlib coverage analysis, project-level gap reports |
| `import Meridian.Domain.PDE` | Distributional derivative tactics, Sobolev exponent arithmetic, Biot-Savart connection automation, curvature bound tactics |
| `import Meridian` | Everything |

## Core Commands

```lean
-- Extract all sorries into standalone lemma stubs
#sorry_extract

-- Build dependency graph (outputs DOT format)
#dep_graph

-- Sorry inventory with auto-categorisation
#sorry_inventory

-- Extract theorems with metadata
#extract_theorems

-- Verify a candidate proof against a sorry
#verify_proof declName

-- Structural transforms
#theorem2sorry
#normalize
#rename oldName newName

-- Counterexample search
#disprove declName
```

## Search Tactics

```lean
-- Suggest tactics for the current goal
meridian_suggest

-- Multi-step proof search (IDA* with memoization)
meridian_search (heartbeats := 400000)

-- Decompose goal into sub-lemmas
meridian_decompose

-- Diagnose type-class synthesis failure
#instance_debug SomeTypeClass
```

## Analysis Commands

```lean
-- Find near-miss Mathlib lemmas for a sorry
#mathlib_coverage declName

-- Project-level gap report
#gap_report
```

## Domain Tactics (PDE)

```lean
-- Distributional derivative / weak formulation
meridian_distrib

-- Sobolev exponent arithmetic
meridian_sobolev

-- Biot-Savart connection automation
meridian_biot_savart
meridian_connection

-- Curvature and helicity
meridian_curvature
meridian_helicity
```

## License

Apache 2.0. Copyright 2026 Alejandro Jose Soto Franco.

## Why not AXLE?

AXLE is a hosted API with no privacy policy, no terms of service, and no data retention disclosure. Your proof code gets sent to third-party servers. Meridian runs entirely on your machine.
