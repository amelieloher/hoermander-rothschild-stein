-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module
public import RothschildStein.L1.WeightedJetClasses
@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set
namespace RothschildStein.L1

/-- A smooth field zero at the origin starts every finite weight
induction at degree zero, regardless of the coefficient thresholds. -/
theorem circleFieldJetClass_zero_order_of_zero {N : ℕ}
    (Ω : Set (Fin N → ℝ)) (ω : Fin N → ℕ) (a : ℝ)
    (R : (Fin N → ℝ) → (Fin N → ℝ))
    (hR : ContDiffOn ℝ (⊤ : ℕ∞) R Ω) (hR0 : R 0 = 0) :
    circleFieldJetClass Ω ω a 0 R := by
  refine ⟨⟨hR, ?_⟩, hR0⟩
  intro j J hJ _
  have he : J = [] := List.length_eq_zero_iff.mp (by omega)
  subst J
  change R 0 j = 0
  rw [hR0]
  rfl
end RothschildStein.L1
