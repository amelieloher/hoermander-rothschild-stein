-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module
public import RothschildStein.L1.RadialEulerCorrectionWeight
public import RothschildStein.L1.RadialEulerComparison
public import RothschildStein.L1.RadialJacobiIdentity
@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set TopologicalSpace
open scoped BigOperators
namespace RothschildStein.L1

/-- The exact radial Euler identity upgrades coordinate commutators by
one jet order when homogeneous basis commutators retain that order. -/
theorem radial_coordinate_bracket_weight_step_of_basis_brackets {N q : ℕ}
    (Ω : Opens (Fin N → ℝ)) (h0 : (0 : Fin N → ℝ) ∈ Ω)
    (ω : Fin N → ℕ) (Z : Fin N → (Fin N → ℝ) → (Fin N → ℝ))
    (hZ : ∀ k, fieldJetClass Ω ω (-(ω k : ℝ)) (q+1) (Z k))
    (hZ0 : ∀ k, Z k 0 = Pi.single k 1)
    (hrad : ∀ u ∈ Ω, ∑ k, u k • Z k u = u)
    (hB : ∀ j k, fieldJetClass Ω ω (-(ω j : ℝ) - ω k) (q+1)
      (VectorField.lieBracket ℝ (Z j) (Z k))) (i j : Fin N) :
    fieldJetClass Ω ω (-(ω i : ℝ) - ω j) (q+1)
      (VectorField.lieBracket ℝ (Z j) (fun _ => Pi.single i 1)) := by
  let W := VectorField.lieBracket ℝ (Z j) (fun _ => Pi.single i 1)
  have hW : fieldJetClass Ω ω (-(ω i : ℝ) - ω j) q W := by
    have hh := fieldJetClass_lieBracket Ω h0 (hZ j)
      (fieldJetClass_coordinateVector (p := q+1) Ω ω i)
    convert hh using 1; try rfl
    ring
  have hji : fieldJetClass Ω ω (-(ω i : ℝ) - ω j) (q+1)
      (VectorField.lieBracket ℝ (Z j) (Z i)) := by
    convert hB j i using 1; try rfl
    ring
  have hs := fieldJetClass_add Ω h0 (fieldJetClass_add Ω h0 hji
    (radial_coefficient_bracket_error_weight Ω h0 ω Z hZ hZ0 i j))
    (radial_differentiated_bracket_term_weight Ω h0 ω Z hB i j)
  have hs' : fieldJetClass Ω ω (-(ω i : ℝ) - ω j) (q+1)
      (fun u => VectorField.lieBracket ℝ (Z j) (Z i) u +
        (∑ k, (Z j u k - (Pi.single j (1 : ℝ) : Fin N → ℝ) k) •
          VectorField.lieBracket ℝ (fun _ => Pi.single i 1) (Z k) u) +
        ∑ k, u k • VectorField.lieBracket ℝ (fun _ => Pi.single i 1)
          (VectorField.lieBracket ℝ (Z j) (Z k)) u) := by
    exact hs
  have ht := fieldJetClass_sub Ω h0 hs'
    (radial_euler_correction_weight Ω h0 ω Z hZ hZ0 hW)
  apply (fieldJetClass_jetEulerOperator_iff Ω h0 ω _ W hW.1).mp
  apply fieldJetClass_congr Ω h0 ht
  intro u hu
  rw [jetEulerOperator_eq_frame_sub_error Z W u
    (fun k => ((hZ k).1.contDiffAt (Ω.isOpen.mem_nhds hu)).differentiableAt (by simp))]
  rw [radial_frame_euler_bracket_identity Ω Z (fun k => (hZ k).1) hrad hu i j]
end RothschildStein.L1
