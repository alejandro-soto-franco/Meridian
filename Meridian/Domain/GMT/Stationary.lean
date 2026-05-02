/-
Copyright 2026 Alejandro Jose Soto Franco. Licensed under Apache 2.0.
-/
import Meridian.Domain.GMT.FirstVariation

/-!
# Stationary Varifolds

A varifold `V` is *stationary* if its first variation vanishes on every
compactly supported `C¹` vector field: `δV(X) = 0` for all such `X`. Stationary
varifolds are the weak-solution class for the minimal-surface equation and the
starting point of Allard regularity theory.

## Main declarations

* `Meridian.Domain.GMT.Varifold.IsStationary` : the predicate.
* `Meridian.Domain.GMT.Varifold.IsStationary.zero` : the zero varifold is stationary.
-/

namespace Meridian.Domain.GMT

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

namespace Varifold

variable {k : ℕ}

/-- A varifold `V` is stationary if its first variation annihilates every
compactly supported `C¹` vector field. -/
def IsStationary (V : Meridian.Domain.GMT.Varifold E k) : Prop :=
  ∀ X : E → E, ContDiff ℝ 1 X → HasCompactSupport X → V.firstVariation X = 0

/-- The zero varifold (measure = 0) is stationary: every first variation is zero. -/
theorem IsStationary.of_measure_zero (V : Meridian.Domain.GMT.Varifold E k)
    (h : V.measure = 0) : V.IsStationary := by
  sorry -- BLOCKER: `firstVariation` integrates against `V.measure = 0`, so result is 0. Unfolds after firstVariation definition lands.

end Varifold

end Meridian.Domain.GMT
