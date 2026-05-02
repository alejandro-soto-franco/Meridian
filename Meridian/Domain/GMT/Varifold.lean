/-
Copyright 2026 Alejandro Jose Soto Franco. Licensed under Apache 2.0.
-/
import Mathlib.MeasureTheory.Measure.Regular
import Mathlib.Analysis.InnerProductSpace.Basic
import Meridian.Domain.GMT.Rectifiable

/-!
# Varifolds

A `k`-varifold on `E` is a Radon measure on `E × G(k, E)`, where `G(k, E)` is
the Grassmannian of unoriented `k`-planes. For v0.1 we parameterise a varifold
by the pair (ambient space, dimension) and expose its `mass` (the pushforward
to `E`) and its `support`. The full Grassmannian is represented as an opaque
type `GrassmannianAux` pending a dedicated Mathlib contribution; every theorem
touching tangent planes carries a named blocker.

## References

Simon, *Lectures on Geometric Measure Theory*, Chapter 4.
Allard, *On the First Variation of a Varifold*, Ann. of Math. 1972.
-/

namespace Meridian.Domain.GMT

open MeasureTheory

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-- Placeholder for the Grassmannian `G(k, E)` of unoriented `k`-planes in `E`.
Blocker: a first-class `Grassmannian` type with its smooth manifold structure
should land in Mathlib before this is unfolded. -/
def GrassmannianAux (E : Type*) (_k : ℕ) [NormedAddCommGroup E] [InnerProductSpace ℝ E] : Type _ :=
  { S : Submodule ℝ E // True }

/-- The Grassmannian placeholder carries the trivial measurable structure for
v0.1. Refined once `Grassmannian` has a canonical smooth structure in Mathlib. -/
instance (E : Type*) (k : ℕ) [NormedAddCommGroup E] [InnerProductSpace ℝ E] :
    MeasurableSpace (GrassmannianAux E k) := ⊤

/-- A `k`-varifold on an ambient space `E` is a Radon measure on
`E × G(k, E)` with finite total mass. -/
structure Varifold (E : Type*) (k : ℕ)
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] where
  /-- Underlying Radon measure on the product of ambient space and Grassmannian. -/
  measure : Measure (E × GrassmannianAux E k)
  /-- Finiteness of total mass. -/
  finite : IsFiniteMeasure measure

namespace Varifold

variable {k : ℕ}

/-- The mass `‖V‖(Ω)` of a varifold on a measurable set `Ω`. -/
noncomputable def mass (V : Meridian.Domain.GMT.Varifold E k) (Ω : Set E) : ENNReal :=
  V.measure (Ω ×ˢ (Set.univ : Set (GrassmannianAux E k)))

/-- The support of a varifold is the support of its spatial projection. -/
noncomputable def support (V : Meridian.Domain.GMT.Varifold E k) : Set E :=
  sorry -- BLOCKER: `(V.measure.map Prod.fst).support`, pending cleanup of `Measure.support` API.

/-- The zero varifold has mass zero on every set. -/
theorem mass_zero_of_zero (V : Meridian.Domain.GMT.Varifold E k) (Ω : Set E)
    (h : V.measure = 0) : V.mass Ω = 0 := by
  sorry -- BLOCKER: `Measure.zero_apply` once `mass` unfolds under `h`.

end Varifold

end Meridian.Domain.GMT
