-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H1.PrincipalValueDefs

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
namespace RothschildStein.H3

/-- Left pullback commutes with the actual near-plus-far
principal-value convolution. The identity holds for arbitrary functions,
so it includes the total-integral conventions without extra hypotheses. -/
theorem principalValueConvolution_left_pullback {N : ℕ}
    (G : HomogeneousGroup N) (ν K f : (Fin N → ℝ) → ℝ) (z : Fin N → ℝ) :
    H1.principalValueConvolution G ν K (f ∘ G.mul z) =
      (H1.principalValueConvolution G ν K f) ∘ G.mul z := by
  funext x
  have he (w : Fin N → ℝ) : G.mul z (G.mul x (G.inv w)) =
      G.mul (G.mul z x) (G.inv w) := (G.assoc z x (G.inv w)).symm
  simp only [H1.principalValueConvolution, H1.principalValueNear,
    H1.principalValueFar, Function.comp_def]
  simp_rw [he]

end RothschildStein.H3
