-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.G1.CoordinateEndpointChart
public import RothschildStein.G1.FrameCoordinateEquiv
public import Mathlib.Algebra.BigOperators.Fin

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open scoped BigOperators
namespace RothschildStein.G1

/-- The actual selected coordinate chart has precisely the
nondegenerate bracket-frame equivalence as coefficient derivative.
The finite coordinate list uses each selected slot once (BB p. 35). -/
theorem bracketCoordinateChart_coefficient_derivative {ι : Type*} {n : ℕ}
    (Z : ι → (Fin n → ℝ) → (Fin n → ℝ)) (B : Fin n → ι)
    (x : Fin n → ℝ) (hB : G4.frameDet Z B x ≠ 0)
    (H : Fin n → ℝ × (Fin n → ℝ) → (Fin n → ℝ))
    (hz : ∀ i y, H i (0, y) = y)
    (hH : ∀ i, HasFDerivAt (H i)
      ((ContinuousLinearMap.snd ℝ ℝ (Fin n → ℝ)) +
        (ContinuousLinearMap.toSpanSingleton ℝ (Z (B i) x)).comp
          (ContinuousLinearMap.fst ℝ ℝ (Fin n → ℝ))) (0, x)) :
    (fderiv ℝ (coordinateEndpointChart H (List.finRange n)) (0, x)).comp
      (ContinuousLinearMap.inl ℝ (Fin n → ℝ) (Fin n → ℝ)) =
        (frameCoordinateEquiv Z B x hB : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ)) := by
  have hd := coordinateEndpointChart_hasFDerivAt_zero H hz (fun i => Z (B i) x)
    (List.finRange n) x hH
  rw [hd.fderiv, ← Fin.sum_univ_def]
  apply ContinuousLinearMap.ext
  intro u
  change _ = frameCoordinateEquiv Z B x hB u
  rw [frameCoordinateEquiv_apply]
  simp only [ContinuousLinearMap.comp_apply, add_apply, ContinuousLinearMap.inl_apply,
    ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd', sum_apply,
    ContinuousLinearMap.proj_apply, ContinuousLinearMap.toSpanSingleton_apply, zero_add]

end RothschildStein.G1
