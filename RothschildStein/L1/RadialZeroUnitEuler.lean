-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module
public import RothschildStein.L1.UnitEulerInversion
public import RothschildStein.L1.RadialZeroDifferentiation
@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set TopologicalSpace
open scoped BigOperators
namespace RothschildStein.L1

/-- A zero radial sum expresses the coefficient-one Euler operator
as the coordinate-scaled antisymmetric remainder commutators. -/
theorem radial_zero_unitEuler_identity {N : ℕ} (Ω : Opens (Fin N → ℝ))
    (R : Fin N → (Fin N → ℝ) → (Fin N → ℝ))
    (hR : ∀ k, ContDiffOn ℝ (⊤ : ℕ∞) (R k) Ω)
    (hrad : ∀ u ∈ Ω, ∑ k, u k • R k u = 0)
    {u : Fin N → ℝ} (hu : u ∈ Ω) (i : Fin N) :
    unitJetEulerOperator (R i) u =
      ∑ k, u k • (VectorField.lieBracket ℝ (R k) (fun _ => Pi.single i 1) u -
        VectorField.lieBracket ℝ (R i) (fun _ => Pi.single k 1) u) := by
  have he := (radial_zero_differential_identity Ω R hR hrad hu i).symm
  have hi (k : Fin N) : VectorField.lieBracket ℝ (fun _ : Fin N → ℝ => Pi.single i 1)
      (R k) u = -VectorField.lieBracket ℝ (R k) (fun _ => Pi.single i 1) u :=
    VectorField.lieBracket_swap
  simp only [hi,smul_neg,Finset.sum_neg_distrib] at he
  have hRi : R i u = ∑ k, u k • VectorField.lieBracket ℝ (R k)
      (fun _ => Pi.single i 1) u := by
    exact eq_of_sub_eq_zero (by simpa only [sub_eq_add_neg] using he)
  have hk (k : Fin N) : VectorField.lieBracket ℝ (fun _ : Fin N → ℝ => Pi.single k 1)
      (R i) u = -VectorField.lieBracket ℝ (R i) (fun _ => Pi.single k 1) u :=
    VectorField.lieBracket_swap
  simp only [unitJetEulerOperator,hk,smul_neg,Finset.sum_neg_distrib,
    smul_sub,Finset.sum_sub_distrib]
  exact congrArg (fun v => v - ∑ k, u k • VectorField.lieBracket ℝ (R i)
    (fun _ => Pi.single k 1) u) hRi
end RothschildStein.L1
