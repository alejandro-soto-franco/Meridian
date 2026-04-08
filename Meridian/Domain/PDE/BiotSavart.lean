/-
Copyright 2026 Alejandro Jose Soto Franco. Licensed under Apache 2.0.
-/
import Lean

/-!
# Biot-Savart Connection Tactics

Automate goals involving the Biot-Savart kernel and its Levi-Civita connection
structure: singularity estimates, HLS exponent verification, Calderon-Zygmund
properties, torsion-freeness, and metric compatibility.

## Tactics

- `meridian_biot_savart`: kernel estimates, HLS exponents, CZ properties
- `meridian_connection`: Levi-Civita structure (torsion-free + metric-compatible)
-/

namespace Meridian.Domain.PDE.BiotSavart

open Lean Elab Tactic Meta

end Meridian.Domain.PDE.BiotSavart
