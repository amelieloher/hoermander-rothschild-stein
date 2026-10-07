-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.P1.PaddingFieldSmoothness

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
open Set
namespace RothschildStein.P1

/-- The continuous linear base projection has exactly the
`basePoint` preimage domain. -/
theorem paddingBaseCLM_preimage_eq (n d : ℕ) (Ω : Set (Fin n → ℝ)) :
    (paddingBaseCLM n d) ⁻¹' Ω = basePoint ⁻¹' Ω := rfl

/-- The complete padded family is smooth on every domain
projecting into the original coefficient domain. -/
theorem contDiffOn_paddingVectorFields_projection {q n d : ℕ}
    (Ω : Set (Fin n → ℝ)) (U : Set (Fin (n + d) → ℝ))
    (hU : U ⊆ basePoint ⁻¹' Ω)
    (X : Fin (q + 1) → (Fin n → ℝ) → (Fin n → ℝ))
    (hX : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (X i) Ω) :
    ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (paddingVectorFields (d := d) X i) U :=
  fun i => (contDiffOn_paddingVectorFields Ω X hX i).mono
    ((paddingBaseCLM_preimage_eq n d Ω).symm ▸ hU)

end RothschildStein.P1
