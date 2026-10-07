-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module
public import RothschildStein.L1.WeightedFieldAddition
public import RothschildStein.L1.WeightedCircleAction
public import RothschildStein.L1.CoordinateFieldJetClasses
@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set TopologicalSpace
open scoped BigOperators
namespace RothschildStein.L1

/-- The varying frame coefficients multiply coordinate brackets without
losing a jet order, because the coefficient errors vanish at the origin. -/
theorem radial_coefficient_bracket_error_weight {N q : ℕ}
    (Ω : Opens (Fin N → ℝ)) (h0 : (0 : Fin N → ℝ) ∈ Ω)
    (ω : Fin N → ℕ) (Z : Fin N → (Fin N → ℝ) → (Fin N → ℝ))
    (hZ : ∀ k, fieldJetClass Ω ω (-(ω k : ℝ)) (q+1) (Z k))
    (hZ0 : ∀ k, Z k 0 = Pi.single k 1) (i j : Fin N) :
    fieldJetClass Ω ω (-(ω i : ℝ) - ω j) (q+1)
      (fun u => ∑ k, (Z j u k - (Pi.single j (1 : ℝ) : Fin N → ℝ) k) •
        VectorField.lieBracket ℝ (fun _ => Pi.single i 1) (Z k) u) := by
  apply fieldJetClass_sum Ω h0 ω (-(ω i : ℝ) - ω j) Finset.univ
  intro k _
  have hc := circleScalarJetClass_coordinate_of_circleField
    (circleFieldJetClass_coordinate_difference Ω h0 ω j (Z j) (hZ j) (hZ0 j)) k
  have hb := fieldJetClass_lieBracket Ω h0
    (fieldJetClass_coordinateVector (p := q+1) Ω ω i) (hZ k)
  have hp := (circleFieldJetClass_smul_scalar_zero Ω h0 hc hb).1
  convert hp using 1; try rfl
  ring

/-- Coordinate times differentiated basis brackets has the full next
jet order when the homogeneous basis bracket has that order. -/
theorem radial_differentiated_bracket_term_weight {N q : ℕ}
    (Ω : Opens (Fin N → ℝ)) (h0 : (0 : Fin N → ℝ) ∈ Ω)
    (ω : Fin N → ℕ) (Z : Fin N → (Fin N → ℝ) → (Fin N → ℝ))
    (hB : ∀ j k, fieldJetClass Ω ω (-(ω j : ℝ) - ω k) (q+1)
      (VectorField.lieBracket ℝ (Z j) (Z k))) (i j : Fin N) :
    fieldJetClass Ω ω (-(ω i : ℝ) - ω j) (q+1)
      (fun u => ∑ k, u k • VectorField.lieBracket ℝ (fun _ => Pi.single i 1)
        (VectorField.lieBracket ℝ (Z j) (Z k)) u) := by
  apply fieldJetClass_sum Ω h0 ω (-(ω i : ℝ) - ω j) Finset.univ
  intro k _
  have hb := fieldJetClass_lieBracket Ω h0
    (fieldJetClass_coordinateVector (p := q+1) Ω ω i) (hB j k)
  have hp := (circleFieldJetClass_smul_scalar_zero Ω h0
    (circleScalarJetClass_coordinate (p := q+1) Ω ω k) hb).1
  convert hp using 1; try rfl
  ring
end RothschildStein.L1
