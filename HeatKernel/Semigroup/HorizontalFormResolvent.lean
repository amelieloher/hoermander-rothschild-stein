-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Semigroup.FormResolvent
public import HeatKernel.Form.GraphForm

/-! # Riesz resolvent of the horizontal energy graph

The graph inner product is the sum of the spatial inner product and horizontal energy.
Density on an arbitrary open set is retained as an explicit hypothesis where required.
-/

@[expose] public section
noncomputable section
open Set TopologicalSpace

namespace HeatKernel
variable {N q : ℕ} (U : Opens (Fin N → ℝ))
    (X : Fin q → (Fin N → ℝ) → (Fin N → ℝ))

theorem energyGraph_inner_eq (u v : energyGraph U X) :
    inner ℝ u v = inner ℝ (energyInclusion U X u) (energyInclusion U X v) +
      horizontalEnergy U X u v := by
  change inner ℝ (u : GradientSpace U q) (v : GradientSpace U q) = _
  exact WithLp.prod_inner_apply _ _

theorem norm_energyInclusion_le_one : ‖energyInclusion U X‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro u
  have h := energyGraph_norm_sq_eq U X u
  have he := horizontalEnergy_self_nonneg U X u
  have hn := norm_nonneg u
  have hj := norm_nonneg (energyInclusion U X u)
  simp only [one_mul]
  nlinarith

/-- The spatial resolvent associated with the horizontal energy form. -/
def horizontalFormResolvent : SpatialL2 U →L[ℝ] SpatialL2 U :=
  formResolvent (V := energyGraph U X) (H := SpatialL2 U) (energyInclusion U X)

theorem horizontalFormResolvent_isPositive : (horizontalFormResolvent U X).IsPositive :=
  formResolvent_isPositive _

theorem horizontalFormResolvent_isSelfAdjoint : IsSelfAdjoint (horizontalFormResolvent U X) :=
  formResolvent_isSelfAdjoint _

theorem norm_horizontalFormResolvent_le_one : ‖horizontalFormResolvent U X‖ ≤ 1 :=
  norm_formResolvent_le_one _ (norm_energyInclusion_le_one U X)

theorem horizontalFormResolvent_injective_of_denseRange
    (hdense : DenseRange (energyInclusion U X)) :
    Function.Injective (horizontalFormResolvent U X) :=
  formResolvent_injective_of_denseRange _ hdense

theorem denseRange_energyInclusion_univ (hX : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (X i)) :
    DenseRange (energyInclusion ⊤ X) := denseRange_energyGraph_fst X hX

theorem horizontalFormResolvent_univ_injective (hX : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (X i)) :
    Function.Injective (horizontalFormResolvent ⊤ X) :=
  horizontalFormResolvent_injective_of_denseRange ⊤ X (denseRange_energyInclusion_univ X hX)

theorem horizontalFormEquation_iff_resolvent_eq
    (hX : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (X i) (U : Set (Fin N → ℝ)))
    (u : energyGraph U X) (g : SpatialL2 U) :
    (∀ v, horizontalEnergy U X u v = inner ℝ g (energyInclusion U X v)) ↔
      horizontalFormResolvent U X (energyInclusion U X u + g) = energyInclusion U X u := by
  simpa only [horizontalFormResolvent, energyGraph_inner_eq, add_sub_cancel_left] using
    formEquation_iff_resolvent_eq_of_injective (V := energyGraph U X) (H := SpatialL2 U) (energyInclusion U X)
      (energyInclusion_injective U X hX) u g

end HeatKernel
