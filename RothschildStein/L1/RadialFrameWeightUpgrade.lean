-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module
public import RothschildStein.L1.RadialCoordinateBracketWeightStep
@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set TopologicalSpace
open scoped BigOperators
namespace RothschildStein.L1

/-- The differentiated radial identity upgrades each frame field once
its coordinate commutators have the preceding finite jet order. -/
theorem radial_frame_weight_upgrade_of_coordinate_brackets {N q : ℕ}
    (Ω : Opens (Fin N → ℝ)) (h0 : (0 : Fin N → ℝ) ∈ Ω)
    (ω : Fin N → ℕ) (Z : Fin N → (Fin N → ℝ) → (Fin N → ℝ))
    (hZ : ∀ k, ContDiffOn ℝ (⊤ : ℕ∞) (Z k) Ω)
    (hrad : ∀ u ∈ Ω, ∑ k, u k • Z k u = u)
    (hB : ∀ i j, fieldJetClass Ω ω (-(ω i : ℝ) - ω j) q
      (VectorField.lieBracket ℝ (Z j) (fun _ => Pi.single i 1))) (i : Fin N) :
    fieldJetClass Ω ω (-(ω i : ℝ)) (q+1) (Z i) := by
  have hs := fieldJetClass_sum Ω h0 ω (-(ω i : ℝ)) Finset.univ
    (fun k u => u k • VectorField.lieBracket ℝ (Z k) (fun _ => Pi.single i 1) u)
    (by
      intro k _
      have hp := (circleFieldJetClass_smul_scalar_zero Ω h0
        (circleScalarJetClass_coordinate (p := q+1) Ω ω k) (hB i k)).1
      convert hp using 1; try rfl
      ring)
  have ha := fieldJetClass_add Ω h0
    (fieldJetClass_coordinateVector (p := q+1) Ω ω i) hs
  apply fieldJetClass_congr Ω h0 ha
  intro u hu
  have he := radial_frame_coordinate_identity Ω Z hZ hrad hu i
  have hh (k : Fin N) : VectorField.lieBracket ℝ (fun _ : Fin N → ℝ => Pi.single i 1)
      (Z k) u = -VectorField.lieBracket ℝ (Z k) (fun _ => Pi.single i 1) u :=
    VectorField.lieBracket_swap
  simp_rw [hh, smul_neg] at he
  rw [Finset.sum_neg_distrib] at he
  change Z i u = (Pi.single i (1 : ℝ) : Fin N → ℝ) + _
  have rearrange (a b c : Fin N → ℝ) (h : a = b + -c) : b = a + c := by
    rw [h]
    abel
  exact rearrange _ _ _ he
end RothschildStein.L1
