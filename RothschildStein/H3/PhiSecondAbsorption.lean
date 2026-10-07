-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H3.PhiInterpolationToReal

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
namespace RothschildStein.H3
open scoped ENNReal

/-- Step 2: the actual extended Phi bounds yield the
absorbed real second and first estimates with the exact constants. -/
theorem phi_second_absorbed_bounds {P₀ P₁ P₂ : ℝ≥0∞} {r C a b cE δ F : ℝ}
    (hP₀ : P₀ ≠ ⊤) (hP₂ : P₂ ≠ ⊤)
    (hC : 0 ≤ C) (ha : 0 ≤ a) (hb : 0 ≤ b) (hcE : 0 ≤ cE)
    (hF : 0 ≤ F) (hδ : 0 < δ) (hsmall : a*δ ≤ 1/2)
    (hsecond : P₂ ≤ ENNReal.ofReal (C*r^2/4*F + a*P₁.toReal + b*P₀.toReal))
    (hfirst : P₁ ≤ ENNReal.ofReal δ*P₂ + ENNReal.ofReal (cE/δ)*P₀) :
    P₂.toReal ≤ C*r^2/2*F + 2*(b+a*cE/δ)*P₀.toReal ∧
      P₁.toReal ≤ δ*(C*r^2/2*F + 2*(b+a*cE/δ)*P₀.toReal) + cE/δ*P₀.toReal := by
  have hs := ENNReal.toReal_mono ENNReal.ofReal_ne_top hsecond
  rw [ENNReal.toReal_ofReal (by positivity)] at hs
  have hf := phi_interpolation_toReal hP₀ hP₂ hδ hcE hfirst
  have h₂ := localEstimate_scalar_absorption ENNReal.toReal_nonneg hsmall ha hs hf
  refine ⟨h₂, hf.trans ?_⟩
  exact add_le_add (mul_le_mul_of_nonneg_left h₂ hδ.le) le_rfl

end RothschildStein.H3
