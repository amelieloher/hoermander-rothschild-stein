-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H3.IntrinsicWordTransport
public import RothschildStein.G2.InvariantFields

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
open Set TopologicalSpace
namespace RothschildStein.H3
variable {N m : ℕ} (G : HomogeneousGroup N)

/-- Left translation commutes with the fixed single-field
intrinsic derivative, without classical smoothness of the scalar input. -/
theorem hasIntrinsicDeriv_leftTranslation
    (Ω : Opens (Fin N → ℝ)) (X : (Fin N → ℝ) → (Fin N → ℝ))
    (hX : ContDiff ℝ (⊤ : ℕ∞) X) (hleft : G2.IsLeftInvariantField G X)
    (z : Fin N → ℝ) {f g : (Fin N → ℝ) → ℝ}
    (hf : hasIntrinsicDeriv Ω X f g) :
    hasIntrinsicDeriv ⟨G.mul z ⁻¹' (Ω : Set (Fin N → ℝ)),
      Ω.isOpen.preimage (G2.contDiff_leftTranslation G z).continuous⟩ X
      (f ∘ G.mul z) (g ∘ G.mul z) := by
  simpa only [one_mul, Function.comp_def] using
    hasIntrinsicDeriv_scaled_pullback Ω (G.mul z) X X one_ne_zero
      (G2.contDiff_leftTranslation G z) hX
      (fun x => by simpa only [one_smul] using hleft z x) hf

end RothschildStein.H3
