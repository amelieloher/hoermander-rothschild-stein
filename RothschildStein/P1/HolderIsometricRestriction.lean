-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.Definitions.holderENorm

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public section
noncomputable section
open Set
open scoped ENNReal
namespace RothschildStein.P1

/-- A distance-preserving map of output sets does not increase the
Hölder seminorm. The metric domains may be larger than the output sets. -/
theorem holderSeminorm_comp_le_of_isometry {n N : ℕ}
    (V : Set (Fin n → ℝ)) (U : Set (Fin N → ℝ))
    (d : (Fin n → ℝ) → (Fin n → ℝ) → ℝ≥0∞)
    (D : (Fin N → ℝ) → (Fin N → ℝ) → ℝ≥0∞)
    (j : (Fin n → ℝ) → (Fin N → ℝ)) (hj : MapsTo j V U)
    (he : ∀ x ∈ V, ∀ y ∈ V, D (j x) (j y) = d x y)
    (α : ℝ) (f : (Fin N → ℝ) → ℝ) :
    holderSeminorm d α V (fun x => f (j x)) ≤ holderSeminorm D α U f := by
  unfold holderSeminorm
  apply le_sInf
  intro C hC
  apply sInf_le
  refine ⟨hC.1, ?_⟩
  intro x hx y hy hxy
  have h := hC.2 (j x) (hj hx) (j y) (hj hy) ((he x hx y hy).symm ▸ hxy)
  simpa only [he x hx y hy] using h

/-- The full Hölder norm does not increase under an isometric map of
output sets, independently of the ambient metric domains. -/
theorem holderENorm_comp_le_of_isometry {n N : ℕ}
    (V : Set (Fin n → ℝ)) (U : Set (Fin N → ℝ))
    (d : (Fin n → ℝ) → (Fin n → ℝ) → ℝ≥0∞)
    (D : (Fin N → ℝ) → (Fin N → ℝ) → ℝ≥0∞)
    (j : (Fin n → ℝ) → (Fin N → ℝ)) (hj : MapsTo j V U)
    (he : ∀ x ∈ V, ∀ y ∈ V, D (j x) (j y) = d x y)
    (α : ℝ) (f : (Fin N → ℝ) → ℝ) :
    holderENorm d α V (fun x => f (j x)) ≤ holderENorm D α U f := by
  unfold holderENorm
  apply add_le_add ?_ (holderSeminorm_comp_le_of_isometry V U d D j hj he α f)
  apply iSup_le
  intro x
  exact le_iSup_of_le ⟨j x, hj x.property⟩ le_rfl

end RothschildStein.P1
