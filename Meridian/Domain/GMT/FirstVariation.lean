/-
Copyright 2026 Alejandro Jose Soto Franco. Licensed under Apache 2.0.
-/
import Meridian.Domain.GMT.Varifold
import Mathlib.Analysis.Calculus.ContDiff.Basic

/-!
# First Variation of a Varifold

The first variation of a `k`-varifold `V` under a compactly supported `C¹`
vector field `X : E → E` is

  `δV(X) = ∫ div_S X(x) dV(x, S)`,

where `div_S X(x)` is the divergence of `X` along the tangent plane `S`. The
pairing `δV : C¹_c(E, E) → ℝ` is linear; a varifold is *stationary* iff
`δV ≡ 0`.

## Main declarations

* `Meridian.Domain.GMT.tangentialDivergence` : `div_S X(x)`.
* `Meridian.Domain.GMT.Varifold.firstVariation` : `δV(X)` as a real number.
* `Meridian.Domain.GMT.Varifold.firstVariation_add` : additivity in `X`.
* `Meridian.Domain.GMT.Varifold.firstVariation_smul` : homogeneity in `X`.

## References

Simon, *Lectures on Geometric Measure Theory*, §16.
-/

namespace Meridian.Domain.GMT

open MeasureTheory

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-- Tangential divergence of a `C¹` vector field `X : E → E` along a `k`-plane `S`
at a point `x`. Defined abstractly: projects the Fréchet derivative onto `S`
and takes the trace. Blocker: requires an orthonormal-frame choice on `S`; once
`Grassmannian` has a smooth structure in Mathlib the frame choice is canonical. -/
noncomputable def tangentialDivergence {k : ℕ}
    (X : E → E) (_x : E) (_S : GrassmannianAux E k) : ℝ :=
  sorry -- BLOCKER: trace of `(P_S ∘ fderiv ℝ X x)` on the subspace S; pending Grassmannian API.

namespace Varifold

variable {k : ℕ}

/-- The first variation `δV(X)` of `V` against a `C¹_c` vector field `X`. -/
noncomputable def firstVariation (V : Meridian.Domain.GMT.Varifold E k) (X : E → E) : ℝ :=
  sorry -- BLOCKER: `∫ tangentialDivergence X x S ∂V.measure`; needs `Measure.integral` bound from `V.finite`.

/-- Additivity of the first-variation pairing in the vector-field argument. -/
theorem firstVariation_add (V : Meridian.Domain.GMT.Varifold E k) (X Y : E → E)
    (hX : ContDiff ℝ 1 X) (hY : ContDiff ℝ 1 Y) :
    V.firstVariation (X + Y) = V.firstVariation X + V.firstVariation Y := by
  sorry -- BLOCKER: linearity of `fderiv` + linearity of integral; straightforward once firstVariation unfolds.

/-- Homogeneity of the first-variation pairing in the vector-field argument. -/
theorem firstVariation_smul (V : Meridian.Domain.GMT.Varifold E k) (c : ℝ) (X : E → E)
    (hX : ContDiff ℝ 1 X) :
    V.firstVariation (fun x => c • X x) = c * V.firstVariation X := by
  sorry -- BLOCKER: same pattern as additivity.

end Varifold

end Meridian.Domain.GMT
