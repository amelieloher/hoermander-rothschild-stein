-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module
public import RothschildStein.L1.RadialFrameFullWeight
public import RothschildStein.L1.ModelBasisBracketWeight
@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set TopologicalSpace
namespace RothschildStein.L1
open G3

/-- The constructed model frame satisfies the same full weight theorem
as the actual canonical frame, on every open coefficient domain at zero. -/
theorem model_basis_full_weight {a s : ℕ} {p : Fin a → ℕ+}
    (D : FreeModelData a s p) (Ω : Opens (Fin (freeDimension a s p) → ℝ))
    (h0 : (0 : Fin (freeDimension a s p) → ℝ) ∈ Ω)
    (i : Fin (freeDimension a s p)) :
    fullFieldJetClass Ω D.weight (-(D.weight i : ℝ)) (canonicalWordFrame D D.fields i) := by
  have hX : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (D.fields i) Ω :=
    fun i => (freeModel_fields_smooth D i).contDiffOn
  apply radial_frame_full_weight_of_bracket_closure Ω h0 D.weight
    (canonicalWordFrame D D.fields)
    (fun k => G1.wordBracket_contDiffOn Ω.isOpen D.fields hX (modelBasisWord D k))
  · intro k
    exact modelBasisWord_origin D k
  · intro u _
    exact modelBasisWord_radial D u
  · intro q hW j k
    exact model_basis_bracket_weight_of_basis_weight D Ω h0 hW j k
end RothschildStein.L1
