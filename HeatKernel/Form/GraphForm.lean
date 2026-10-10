-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Form.CoreGradientGraph
public import Mathlib.MeasureTheory.Measure.SeparableMeasure

/-!
# The Hilbert realization of the horizontal energy form

The closed smooth graph carries the form norm. Its coordinate projections are bounded linear
maps, and the energy is the inner product of the gradient projections.
-/

@[expose] public section

noncomputable section

open Set MeasureTheory TopologicalSpace
open scoped ENNReal Topology

namespace HeatKernel

variable {N q : ℕ} (U : Opens (Fin N → ℝ))
    (X : Fin q → (Fin N → ℝ) → (Fin N → ℝ))

/-- Bounded inclusion of the form domain into spatial L². -/
def energyInclusion : energyGraph U X →L[ℝ] SpatialL2 U :=
  (ContinuousLinearMap.fst ℝ (SpatialL2 U) (PiLp 2 (fun _ : Fin q => SpatialL2 U))).comp
    ((WithLp.prodContinuousLinearEquiv 2 ℝ (SpatialL2 U)
      (PiLp 2 (fun _ : Fin q => SpatialL2 U))).toContinuousLinearMap.comp (energyGraph U X).subtypeL)

/-- The horizontal gradient is bounded from the form domain to the derivative Hilbert space. -/
def energyGradient : energyGraph U X →L[ℝ] PiLp 2 (fun _ : Fin q => SpatialL2 U) :=
  (ContinuousLinearMap.snd ℝ (SpatialL2 U) (PiLp 2 (fun _ : Fin q => SpatialL2 U))).comp
    ((WithLp.prodContinuousLinearEquiv 2 ℝ (SpatialL2 U)
      (PiLp 2 (fun _ : Fin q => SpatialL2 U))).toContinuousLinearMap.comp (energyGraph U X).subtypeL)

/-- The horizontal energy is the gradient inner product. -/
def horizontalEnergy (u v : energyGraph U X) : ℝ :=
  inner ℝ (energyGradient U X u) (energyGradient U X v)

/-- Evaluation of the inclusion is the function coordinate. -/
@[simp] theorem energyInclusion_apply (v : energyGraph U X) :
    energyInclusion U X v = (v : GradientSpace U q).fst := rfl

/-- Evaluation of the gradient is the derivative coordinate. -/
@[simp] theorem energyGradient_apply (v : energyGraph U X) :
    energyGradient U X v = (v : GradientSpace U q).snd := rfl

/-- The energy is nonnegative on the diagonal. -/
theorem horizontalEnergy_self_nonneg (u : energyGraph U X) : 0 ≤ horizontalEnergy U X u u :=
  real_inner_self_nonneg

/-- The form norm is exactly the Hilbert graph norm. -/
theorem energyGraph_norm_sq_eq (u : energyGraph U X) :
    ‖u‖ ^ 2 = ‖energyInclusion U X u‖ ^ 2 + horizontalEnergy U X u u := by
  change ‖(u : GradientSpace U q)‖ ^ 2 = _
  rw [WithLp.prod_norm_sq_eq_of_L2]
  simp only [energyInclusion_apply, horizontalEnergy, energyGradient_apply, real_inner_self_eq_norm_sq]

/-- The function inclusion is injective for smooth vector fields. -/
theorem energyInclusion_injective
    (hX : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (X i) (U : Set (Fin N → ℝ))) :
    Function.Injective (energyInclusion U X) := energyGraph_fst_injective U X hX

/-- The form domain is separable, as a subspace of finitely many separable spatial L² spaces. -/
instance : SecondCountableTopology (energyGraph U X) := by
  let : Fact ((2 : ℝ≥0∞) ≠ ⊤) := ⟨by norm_num⟩
  let : IsSeparable (volume.restrict (U : Set (Fin N → ℝ))) := isSeparable_of_sigmaFinite _
  infer_instance

end HeatKernel
