-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.P1.PaddingTestTransportSupported

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
open Set TopologicalSpace
namespace RothschildStein.P1

/-- LF continuous coordinate transport from the
joined carrier to the product carrier. -/
def paddingTestToProductCLM {n d : ℕ} {B : Type*}
    [NormedAddCommGroup B] [NormedSpace ℝ B]
    (U : Opens (Fin (n + d) → ℝ)) :
    _root_.TestFunction U B ⊤ →L[ℝ]
      _root_.TestFunction (paddingProductOpen U) B ⊤ :=
  _root_.TestFunction.mkCLM ℝ (paddingTestToProduct U)
    (fun _ _ => by ext; rfl) (fun _ _ => by ext; rfl) (by
      intro K hK
      have hprod : (K.map (paddingCoordinates n d) (paddingCoordinates n d).continuous :
          Set ((Fin n → ℝ) × (Fin d → ℝ))) ⊆ paddingProductOpen U := by
        intro p hp
        obtain ⟨ξ, hξ, rfl⟩ := hp
        change (paddingCoordinates n d).symm ((paddingCoordinates n d) ξ) ∈ U
        simpa using hK hξ
      let T := (_root_.TestFunction.ofSupportedInCLM ℝ hprod).comp
        (paddingSupportedToProductCLM (B := B) K)
      convert T.continuous using 1
      funext φ
      ext p
      rfl)

end RothschildStein.P1
