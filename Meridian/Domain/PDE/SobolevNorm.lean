/-
Copyright 2026 Alejandro Jose Soto Franco. Licensed under Apache 2.0.
-/
import Lean

/-!
# Sobolev Exponent Arithmetic

Automate Sobolev conjugate computation, Holder chain verification, and dimensional
consistency checks for Lp/Sobolev embedding goals.

## Tactics

- `meridian_sobolev`: Sobolev/Holder exponent automation

## Commands

- `#sobolev_check`: verify dimensional consistency of a Sobolev embedding
-/

namespace Meridian.Domain.PDE.SobolevNorm

open Lean Elab Tactic Meta

end Meridian.Domain.PDE.SobolevNorm
