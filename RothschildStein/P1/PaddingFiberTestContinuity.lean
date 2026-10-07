-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.P1.PaddingTestTransportContinuity
public import RothschildStein.P1.FiberIntegralTestContinuity

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
open Set MeasureTheory TopologicalSpace
namespace RothschildStein.P1

/-- The product-coordinate open set projects into the original
domain whenever the joined-coordinate open set does. -/
theorem paddingProductOpen_subset_base_preimage {n d : ℕ}
    (Ω : Opens (Fin n → ℝ)) (U : Opens (Fin (n + d) → ℝ))
    (hU : (U : Set (Fin (n + d) → ℝ)) ⊆ basePoint ⁻¹' (Ω : Set (Fin n → ℝ))) :
    (paddingProductOpen U : Set ((Fin n → ℝ) × (Fin d → ℝ))) ⊆
      Prod.fst ⁻¹' (Ω : Set (Fin n → ℝ)) := by
  intro p hp
  have h := hU hp
  change basePoint (paddingJoinCLM n d p) ∈ Ω at h
  rw [← paddingBaseCLM_apply] at h
  rw [paddingJoinCLM_apply, paddingBaseCLM_join] at h
  exact h

/-- LF continuous fiber integration for the
joined-coordinate test carrier. -/
def paddingFiberTestCLM {n d : ℕ} {B : Type*}
    [NormedAddCommGroup B] [NormedSpace ℝ B] [CompleteSpace B]
    (Ω : Opens (Fin n → ℝ)) (U : Opens (Fin (n + d) → ℝ))
    (hU : (U : Set (Fin (n + d) → ℝ)) ⊆ basePoint ⁻¹' (Ω : Set (Fin n → ℝ))) :
    _root_.TestFunction U B ⊤ →L[ℝ] _root_.TestFunction Ω B ⊤ :=
  (fiberIntegralTestCLM Ω (paddingProductOpen U)
    (paddingProductOpen_subset_base_preimage Ω U hU)).comp (paddingTestToProductCLM U)

/-- The joined-coordinate LF map integrates the actual
joined-coordinate test over the added variables. -/
theorem paddingFiberTestCLM_apply {n d : ℕ} {B : Type*}
    [NormedAddCommGroup B] [NormedSpace ℝ B] [CompleteSpace B]
    (Ω : Opens (Fin n → ℝ)) (U : Opens (Fin (n + d) → ℝ))
    (hU : (U : Set (Fin (n + d) → ℝ)) ⊆ basePoint ⁻¹' (Ω : Set (Fin n → ℝ)))
    (φ : _root_.TestFunction U B ⊤) (x : Fin n → ℝ) :
    paddingFiberTestCLM Ω U hU φ x = ∫ z : Fin d → ℝ, φ (joinPoint x z) := by
  change (∫ z, paddingTestToProduct U φ (x, z)) = _
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun z => paddingTestToProduct_apply U φ x z

end RothschildStein.P1
