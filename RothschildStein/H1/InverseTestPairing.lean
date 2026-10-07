-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.G2.ConvolutionSubstitution
public import Mathlib.Analysis.Distribution.TestFunction

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
open Set MeasureTheory
namespace RothschildStein.H1
variable {N : ℕ} (G : HomogeneousGroup N)

/-- Inversion preserves compact smooth scalar tests. -/
theorem compactSmooth_comp_inv {φ : (Fin N → ℝ) → ℝ}
    (hc : ContDiff ℝ (⊤ : ℕ∞) φ) (hs : HasCompactSupport φ) :
    ContDiff ℝ (⊤ : ℕ∞) (φ ∘ G.inv) ∧ HasCompactSupport (φ ∘ G.inv) := by
  let e : (Fin N → ℝ) ≃ₜ (Fin N → ℝ) :=
    { toFun := G.inv, invFun := G.inv,
      left_inv := G2.inv_inv G, right_inv := G2.inv_inv G,
      continuous_toFun := G2.continuous_inv G, continuous_invFun := G2.continuous_inv G }
  exact ⟨hc.comp (G2.contDiff_inv G), hs.comp_homeomorph e⟩

/-- Scalar kernel pairing is the actual convolution
against the inverted test at the identity. -/
theorem groupConvolution_invertedTest_zero (f φ : (Fin N → ℝ) → ℝ) :
    G2.groupConvolution G (φ ∘ G.inv) f 0 = ∫ w, f w * φ w := by
  rw [G2.groupConvolution_def]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun w => by
    simp only [Function.comp_apply, G2.zero_mul, G2.inv_inv]
    exact mul_comm _ _

end RothschildStein.H1
