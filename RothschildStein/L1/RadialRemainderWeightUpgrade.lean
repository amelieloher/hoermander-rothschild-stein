-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module
public import RothschildStein.L1.RadialZeroUnitEuler
public import RothschildStein.L1.WeightedFieldLocality
public import RothschildStein.L1.CoordinateJetClasses
@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set TopologicalSpace
open scoped BigOperators
namespace RothschildStein.L1

/-- Symmetry modulo the strict filtration upgrades the remainder fields.
The coefficient-one Euler inversion avoids an additional differentiated
symmetry calculation. -/
theorem radial_remainder_weight_upgrade_of_symmetry {N q : ℕ}
    (Ω : Opens (Fin N → ℝ)) (h0 : (0 : Fin N → ℝ) ∈ Ω)
    (ω : Fin N → ℕ) (R : Fin N → (Fin N → ℝ) → (Fin N → ℝ))
    (hR : ∀ k, ContDiffOn ℝ (⊤ : ℕ∞) (R k) Ω)
    (hrad : ∀ u ∈ Ω, ∑ k, u k • R k u = 0)
    (hS : ∀ i k, fieldJetClass Ω ω (1 - (ω i : ℝ) - ω k) q
      (fun u => VectorField.lieBracket ℝ (R k) (fun _ => Pi.single i 1) u -
        VectorField.lieBracket ℝ (R i) (fun _ => Pi.single k 1) u)) (i : Fin N) :
    fieldJetClass Ω ω (1 - (ω i : ℝ)) (q+1) (R i) := by
  have hs := fieldJetClass_sum Ω h0 ω (1 - (ω i : ℝ)) Finset.univ
    (fun k u => u k • (VectorField.lieBracket ℝ (R k) (fun _ => Pi.single i 1) u -
      VectorField.lieBracket ℝ (R i) (fun _ => Pi.single k 1) u)) (by
      intro k _
      have hp := (circleFieldJetClass_smul_scalar_zero Ω h0
        (circleScalarJetClass_coordinate (p := q+1) Ω ω k) (hS i k)).1
      convert hp using 1; try rfl
      ring)
  apply (fieldJetClass_unitJetEulerOperator_iff Ω h0 ω _ (R i) (hR i)).mp
  apply fieldJetClass_congr Ω h0 hs
  intro u hu
  exact radial_zero_unitEuler_identity Ω R hR hrad hu i
end RothschildStein.L1
