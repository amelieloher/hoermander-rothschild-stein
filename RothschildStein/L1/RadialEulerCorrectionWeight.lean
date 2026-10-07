-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module
public import RothschildStein.L1.RadialBracketWeightTerms
@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set TopologicalSpace
open scoped BigOperators
namespace RothschildStein.L1

/-- Replacing the radial frame by the constant coordinate frame in the
Euler derivative creates a circle-field error of the required next order. -/
theorem radial_euler_correction_weight {N q : ℕ}
    (Ω : Opens (Fin N → ℝ)) (h0 : (0 : Fin N → ℝ) ∈ Ω)
    (ω : Fin N → ℕ) (Z : Fin N → (Fin N → ℝ) → (Fin N → ℝ))
    (hZ : ∀ k, fieldJetClass Ω ω (-(ω k : ℝ)) (q+1) (Z k))
    (hZ0 : ∀ k, Z k 0 = Pi.single k 1)
    {b : ℝ} {W : (Fin N → ℝ) → (Fin N → ℝ)}
    (hW : fieldJetClass Ω ω b q W) :
    fieldJetClass Ω ω b (q+1)
      (fun u => ∑ k, u k • VectorField.lieBracket ℝ
        (fun v => Z k v - Pi.single k 1) W u) := by
  apply fieldJetClass_sum Ω h0 ω b Finset.univ
  intro k _
  have hb := fieldJetClass_lieBracket_circle Ω h0
    (circleFieldJetClass_coordinate_difference Ω h0 ω k (Z k) (hZ k) (hZ0 k)) hW
  have hp := (circleFieldJetClass_smul_scalar_zero Ω h0
    (circleScalarJetClass_coordinate (p := q+1) Ω ω k) hb).1
  convert hp using 1; try rfl
  ring
end RothschildStein.L1
