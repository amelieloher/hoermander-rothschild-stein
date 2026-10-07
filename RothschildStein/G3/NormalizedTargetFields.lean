-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module
public import RothschildStein.G3.NormalizedTargetDilation
@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set TopologicalSpace
namespace RothschildStein.G3

/-- The retained formal word sum is exactly the source sum of nested field brackets. -/
theorem finiteLieField_normalizedWordTarget {a s N : ℕ} {p : Fin a → ℕ+}
    (D : FreeModelData a s p) (Ω : Opens (Fin N → ℝ))
    (X : Fin a → (Fin N → ℝ) → (Fin N → ℝ))
    (hX : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (X i) Ω)
    (b : List (Fin a) → ℝ) {x : Fin N → ℝ} (hx : x ∈ Ω) :
    finiteLieField D X (normalizedWordTarget (s := s) (p := p) b) x =
      ((correctionWordEnumeration a s p s).map (fun I => b I • wordBracket X I x)).sum := by
  let F : formalSpan a s p →ₗ[ℝ] (Fin N → ℝ) :=
    (LinearMap.proj x).comp (finiteLieFieldLinear D X)
  have hmap : ∀ U : List (formalSpan a s p), F U.sum = (U.map F).sum := by
    intro U
    induction U with
    | nil => exact F.map_zero
    | cons u U ih => simp only [List.sum_cons,List.map_cons,map_add,ih]
  change F (((correctionWordEnumeration a s p s).map (fun I => b I • wordLieElement I)).sum) = _
  rw [hmap,List.map_map]
  congr 1
  apply List.map_congr_left
  intro I hI
  rw [Function.comp_apply,map_smul]
  change b I • finiteLieField D X (wordLieElement I) x = _
  rw [finiteLieField_word D Ω X hX I (correctionWordEnumeration_mem I hI).1
    (correctionWordEnumeration_mem I hI).2 hx]
end RothschildStein.G3
