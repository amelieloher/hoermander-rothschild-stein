-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.P1.FiberIntegralSupportedDefs

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
open Set MeasureTheory TopologicalSpace WithSeminorms
namespace RothschildStein.P1

/-- Fiber integration is continuous on every fixed compact
support space, by the derivative seminorm bounds. -/
theorem continuous_fiberIntegralSupportedLM {n d : ℕ} {B : Type*}
    [NormedAddCommGroup B] [NormedSpace ℝ B] [CompleteSpace B]
    (K : Compacts ((Fin n → ℝ) × (Fin d → ℝ))) :
    Continuous (fiberIntegralSupportedLM (B := B) K) := by
  apply continuous_of_isBounded
    (ContDiffMapSupportedIn.withSeminorms ℝ ((Fin n → ℝ) × (Fin d → ℝ)) B ⊤ K)
    (ContDiffMapSupportedIn.withSeminorms ℝ (Fin n → ℝ) B ⊤
      (K.map Prod.fst continuous_fst)) _ (.of_real fun i => ?_)
  refine ⟨{i}, volume.real (Prod.snd '' (K : Set ((Fin n → ℝ) × (Fin d → ℝ)))), ?_⟩
  intro φ
  simpa using seminorm_fiberIntegralSupportedLM_le K i φ

/-- The continuous real-linear fiber integration map on a
fixed compact support space. -/
def fiberIntegralSupportedCLM {n d : ℕ} {B : Type*}
    [NormedAddCommGroup B] [NormedSpace ℝ B] [CompleteSpace B]
    (K : Compacts ((Fin n → ℝ) × (Fin d → ℝ))) :
    ContDiffMapSupportedIn ((Fin n → ℝ) × (Fin d → ℝ)) B ⊤ K →L[ℝ]
      ContDiffMapSupportedIn (Fin n → ℝ) B ⊤ (K.map Prod.fst continuous_fst) where
  toLinearMap := fiberIntegralSupportedLM K
  cont := continuous_fiberIntegralSupportedLM K

end RothschildStein.P1
