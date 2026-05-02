/-
Copyright 2026 Alejandro Jose Soto Franco. Licensed under Apache 2.0.
-/
import Mathlib.MeasureTheory.Measure.Hausdorff
import Mathlib.Analysis.InnerProductSpace.Basic

/-!
# Countably `k`-Rectifiable Sets

A set `S ⊆ E` in a finite-dimensional inner product space is countably
`k`-rectifiable if it is `ℋᵏ`-almost covered by countably many Lipschitz images
of bounded subsets of `ℝᵏ`. This is the geometric-measure-theoretic generalisation
of a `k`-dimensional submanifold and is the substrate on which integer-rectifiable
varifolds are defined.

## Main declarations

* `Meridian.Domain.GMT.CountablyRectifiable` : the predicate itself.
* `Meridian.Domain.GMT.CountablyRectifiable.subset` : hereditary under subset.
* `Meridian.Domain.GMT.CountablyRectifiable.union` : closed under countable union.

## References

Simon, *Lectures on Geometric Measure Theory*, Chapter 3.
-/

namespace Meridian.Domain.GMT

open MeasureTheory Set

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-- A set `S ⊆ E` is countably `k`-rectifiable if, up to an `ℋᵏ`-null set,
it is the union of countably many Lipschitz images of subsets of
`EuclideanSpace ℝ (Fin k)`. -/
def CountablyRectifiable (k : ℕ) (S : Set E) : Prop :=
  ∃ (N : Set E) (A : ℕ → Set (EuclideanSpace ℝ (Fin k))) (f : ℕ → EuclideanSpace ℝ (Fin k) → E),
    (MeasureTheory.Measure.hausdorffMeasure (k : ℝ) : Measure E) N = 0 ∧
    (∀ i, ∃ L : NNReal, LipschitzOnWith L (f i) (A i)) ∧
    S ⊆ N ∪ ⋃ i, (f i) '' (A i)

/-- Subsets of rectifiable sets are rectifiable.
Blocker: requires `hausdorffMeasure` monotonicity packaging, straightforward. -/
theorem CountablyRectifiable.subset {k : ℕ} {S T : Set E}
    (hT : CountablyRectifiable k T) (hST : S ⊆ T) : CountablyRectifiable k S := by
  sorry -- BLOCKER: unpack hT, restrict covering to S; needs Mathlib hausdorff lemma `measure_mono_null`.

/-- Countable unions of countably-rectifiable sets are countably rectifiable.
Blocker: reindex the Lipschitz pieces via `Nat.pair`; requires a `Nat`-indexed family flatten. -/
theorem CountablyRectifiable.iUnion {k : ℕ} {S : ℕ → Set E}
    (hS : ∀ n, CountablyRectifiable k (S n)) : CountablyRectifiable k (⋃ n, S n) := by
  sorry -- BLOCKER: diagonal reindexing over ℕ × ℕ; Mathlib `Encodable.decode` pattern.

end Meridian.Domain.GMT
