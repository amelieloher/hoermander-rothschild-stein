-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module
public import RothschildStein.L1.CoordinateBracketCircleWeight
public import RothschildStein.L1.WeightedBracketCircleRight
@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set TopologicalSpace
open scoped BigOperators
namespace RothschildStein.L1

/-- Bracketing a finite-order remainder with the coordinate-scaled
actual frame derivative retains the required strict order. -/
theorem radial_remainder_actual_error_weight {N q : ℕ}
    (Ω : Opens (Fin N → ℝ)) (h0 : (0 : Fin N → ℝ) ∈ Ω)
    (ω : Fin N → ℕ) (Z R : Fin N → (Fin N → ℝ) → (Fin N → ℝ))
    (hZ : ∀ k, fullFieldJetClass Ω ω (-(ω k : ℝ)) (Z k))
    (hR : ∀ k, fieldJetClass Ω ω (1 - (ω k : ℝ)) q (R k)) (i j : Fin N) :
    fieldJetClass Ω ω (1 - (ω i : ℝ) - ω j) q
      (fun u => ∑ k, VectorField.lieBracket ℝ (R j)
        (fun v => v k • VectorField.lieBracket ℝ (fun _ => Pi.single i 1) (Z k) v) u) := by
  apply fieldJetClass_sum Ω h0 ω (1 - (ω i : ℝ) - ω j) Finset.univ
  intro k _
  have hc := circleFieldJetClass_coordinate_times_bracket Ω h0 (hZ k (q+1)) i k
  have hb := fieldJetClass_lieBracket_circle_right Ω h0 (hR j) hc
  convert hb using 1; try rfl
  ring

/-- Replacing the model frame by its origin coordinate vector in the
remainder sum costs only a strict finite-order error. -/
theorem radial_remainder_model_error_weight {N q : ℕ}
    (Ω : Opens (Fin N → ℝ)) (h0 : (0 : Fin N → ℝ) ∈ Ω)
    (ω : Fin N → ℕ) (Y R : Fin N → (Fin N → ℝ) → (Fin N → ℝ))
    (hY : ∀ k, fullFieldJetClass Ω ω (-(ω k : ℝ)) (Y k))
    (hY0 : ∀ k, Y k 0 = Pi.single k 1)
    (hR : ∀ k, fieldJetClass Ω ω (1 - (ω k : ℝ)) q (R k)) (i j : Fin N) :
    fieldJetClass Ω ω (1 - (ω i : ℝ) - ω j) q
      (fun u => ∑ k, VectorField.lieBracket ℝ (fun v => Y j v - Pi.single j 1)
        (fun v => v k • VectorField.lieBracket ℝ (fun _ => Pi.single i 1) (R k) v) u) := by
  apply fieldJetClass_sum Ω h0 ω (1 - (ω i : ℝ) - ω j) Finset.univ
  intro k _
  have hc := circleFieldJetClass_coordinate_times_bracket Ω h0 (hR k) i k
  have hb := fieldJetClass_lieBracket_circle Ω h0
    (circleFieldJetClass_coordinate_difference Ω h0 ω j (Y j) (hY j (q+1)) (hY0 j)) hc.1
  convert hb using 1; try rfl
  ring
end RothschildStein.L1
