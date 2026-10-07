-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import Hormander.F.Coordinates
public import Mathlib.Analysis.Distribution.TemperedDistribution

@[expose] public section

noncomputable section

open MeasureTheory SchwartzMap
open scoped SchwartzMap

namespace Hormander.F

/-- Pull Schwartz tests on the coordinates `Fin N → ℝ` to the Euclidean carrier. -/
def schwartzToEuclideanCLM (N : ℕ) :
    SchwartzMap (Fin N → ℝ) ℂ →L[ℂ] SchwartzMap (E₂ N) ℂ :=
  SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (coordinateEquiv N).symm

/-- Pull Euclidean Schwartz tests back to the coordinates `Fin N → ℝ`. -/
def schwartzToCoordinatesCLM (N : ℕ) :
    SchwartzMap (E₂ N) ℂ →L[ℂ] SchwartzMap (Fin N → ℝ) ℂ :=
  SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (coordinateEquiv N)

/-- Precomposition transports a tempered distribution to the equivalent Euclidean Schwartz
carrier. -/
def temperedToEuclideanCLM (N : ℕ) :
    TemperedDistribution (Fin N → ℝ) ℂ →L[ℂ] TemperedDistribution (E₂ N) ℂ :=
  PointwiseConvergenceCLM.precomp ℂ (schwartzToCoordinatesCLM N)

/-- Measure-preserving transport preserves integrals of arbitrary Bochner-valued integrands. -/
theorem integral_comp_coordinateEquiv {N : ℕ} {A : Type*}
    [NormedAddCommGroup A] [NormedSpace ℝ A] (f : E₂ N → A) :
    ∫ x : Fin N → ℝ, f (coordinateEquiv N x) = ∫ y : E₂ N, f y := by
  exact (coordinateEquiv_measurePreserving N).integral_comp
    (coordinateEquiv N).toHomeomorph.measurableEmbedding f

/-- Almost-everywhere equality is invariant under the volume-preserving coordinate transfer. -/
theorem ae_eq_coordinateEquiv_iff {N : ℕ} {α : Type*} [MeasurableSpace α]
    {f g : E₂ N → α} :
    f =ᵐ[volume] g ↔ (f ∘ coordinateEquiv N) =ᵐ[volume] (g ∘ coordinateEquiv N) := by
  constructor
  · intro h
    exact (coordinateEquiv_measurePreserving N).quasiMeasurePreserving.ae_eq_comp h
  · intro h
    have h' := (coordinateEquiv_symm_measurePreserving N).quasiMeasurePreserving.ae_eq_comp h
    simpa only [Function.comp_def, coordinateEquiv_apply_symm_apply] using h'

end Hormander.F
