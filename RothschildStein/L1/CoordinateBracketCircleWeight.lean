-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module
public import RothschildStein.L1.ZeroOrderCircleField
public import RothschildStein.L1.CoordinateFieldJetClasses
public import RothschildStein.L1.WeightedFieldBrackets
@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set TopologicalSpace
namespace RothschildStein.L1

/-- A coordinate times a coordinate derivative retains the starting
jet order; the zero-degree endpoint is supplied by the coordinate factor. -/
theorem circleFieldJetClass_coordinate_times_bracket {N q : ℕ}
    (Ω : Opens (Fin N → ℝ)) (h0 : (0 : Fin N → ℝ) ∈ Ω)
    {ω : Fin N → ℕ} {a : ℝ} {R : (Fin N → ℝ) → (Fin N → ℝ)}
    (hR : fieldJetClass Ω ω a q R) (i k : Fin N) :
    circleFieldJetClass Ω ω (a - ω i + ω k) q
      (fun u => u k • VectorField.lieBracket ℝ (fun _ => Pi.single i 1) R u) := by
  cases q with
  | zero =>
    have hs : ContDiffOn ℝ (⊤ : ℕ∞)
        (fun u => u k • VectorField.lieBracket ℝ (fun _ => Pi.single i 1) R u) Ω :=
      (contDiffOn_apply ℝ ℝ k Ω).smul
        (lieBracket_contDiffOn Ω _ R contDiffOn_const hR.1)
    exact circleFieldJetClass_zero_order_of_zero Ω ω _ _ hs (by
      change (0 : ℝ) • (VectorField.lieBracket ℝ (fun _ => Pi.single i 1) R 0) = 0
      exact zero_smul ℝ _)
  | succ q =>
    have hb := fieldJetClass_lieBracket Ω h0
      (fieldJetClass_coordinateVector (p := q+1) Ω ω i) hR
    have hp := circleFieldJetClass_smul_scalar_zero Ω h0
      (circleScalarJetClass_coordinate (p := q+1) Ω ω k) hb
    convert hp using 1; try rfl
    ring
end RothschildStein.L1
