-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.G2.DifferentialTranspose

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false

@[expose] public section
noncomputable section
namespace RothschildStein.G2
open MeasureTheory
variable {N : ℕ} (G : HomogeneousGroup N)

/-- Smooth translations are homeomorphisms with inverse translation by the inverse element. -/
def leftTranslationHomeomorph (y : Fin N → ℝ) : (Fin N → ℝ) ≃ₜ (Fin N → ℝ) where
  toFun := G.mul y
  invFun := G.mul (G.inv y)
  left_inv x := by rw [← mul_assoc G, inv_mul G, zero_mul G]
  right_inv x := by rw [← mul_assoc G, mul_inv G, zero_mul G]
  continuous_toFun := (contDiff_leftTranslation G y).continuous
  continuous_invFun := (contDiff_leftTranslation G (G.inv y)).continuous

end RothschildStein.G2
