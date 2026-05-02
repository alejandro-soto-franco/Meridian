/-
Copyright 2026 Alejandro Jose Soto Franco. Licensed under Apache 2.0.
-/
import Meridian.Domain.GMT.Stationary

/-!
# Interior Monotonicity for Stationary Varifolds

Classical theorem: if `V` is a stationary `k`-varifold in an open set `Ω ⊆ E`,
then for every interior point `x₀` the density ratio

  `Θ(V, x₀, r) = ‖V‖(B(x₀, r)) / (ω_k r^k)`

is monotone non-decreasing in `r` on `(0, dist(x₀, ∂Ω))`. This file states the
theorem; the proof is a Stage 3 target (~3-6 months of formalisation work and
the first real research artefact of the Meridian GMT track).

## Main declarations

* `Meridian.Domain.GMT.Varifold.densityRatio` : `‖V‖(B_r) / (ω_k r^k)`.
* `Meridian.Domain.GMT.Varifold.monotonicity_of_stationary` : monotonicity statement.

## References

Simon, *Lectures on Geometric Measure Theory*, §17.
Allard, *On the First Variation of a Varifold*, §5.
-/

namespace Meridian.Domain.GMT

open MeasureTheory Set Metric

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

namespace Varifold

variable {k : ℕ}

/-- The volume of the unit `k`-ball, `ω_k = π^(k/2) / Γ(k/2 + 1)`. -/
noncomputable def unitBallVolume (_k : ℕ) : ℝ :=
  sorry -- BLOCKER: `Real.pi ^ (k / 2 : ℝ) / Real.Gamma (k / 2 + 1)` ; needs half-integer Gamma lemmas.

/-- The density ratio of a varifold at `x₀` at scale `r`. -/
noncomputable def densityRatio (V : Meridian.Domain.GMT.Varifold E k) (x₀ : E) (r : ℝ) : ENNReal :=
  V.mass (Metric.ball x₀ r) / ENNReal.ofReal (unitBallVolume k * r ^ k)

/-- **Monotonicity formula (statement only).** For a stationary `k`-varifold in an
open set `Ω`, the density ratio `r ↦ Θ(V, x₀, r)` is monotone non-decreasing on
`(0, dist(x₀, ∂Ω))`. -/
theorem monotonicity_of_stationary
    (V : Meridian.Domain.GMT.Varifold E k)
    {Ω : Set E} (hΩ : IsOpen Ω) (hV : V.IsStationary)
    {x₀ : E} (hx : x₀ ∈ Ω) {r₁ r₂ : ℝ}
    (hr₁ : 0 < r₁) (hr₁₂ : r₁ ≤ r₂)
    (hr₂ : Metric.ball x₀ r₂ ⊆ Ω) :
    V.densityRatio x₀ r₁ ≤ V.densityRatio x₀ r₂ := by
  sorry -- BLOCKER: classical proof uses δV applied to X(x) = φ(|x-x₀|/r) · (x - x₀);
        -- requires (i) firstVariation on a specific radial X, (ii) ODE/differentiation-under-integral
        -- for the mass ratio. This is a Stage 3 target; see FORMALISATION.md of ~/math/kobe-marshall-stevens.

end Varifold

end Meridian.Domain.GMT
