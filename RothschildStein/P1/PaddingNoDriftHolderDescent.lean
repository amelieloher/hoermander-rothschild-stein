-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.P1.PaddingIntrinsicSlice
public import RothschildStein.P1.PaddingNoDriftHolderSlice
public import RothschildStein.P1.IntrinsicWordReindex
public import RothschildStein.P1.PaddingNoDriftWeightedSpan
public import RothschildStein.S.Sobolev
public import RothschildStein.Definitions.memHolderX
public import RothschildStein.Definitions.intrinsicWordENorm

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public section
noncomputable section
open Set TopologicalSpace
open scoped ENNReal
namespace RothschildStein.P1

/-- Intrinsic derivatives of mapped original words in the
full padded family restrict to the exact original word on each fiber. -/
theorem hasIntrinsicWordDeriv_paddingNoDrift_map_slice {q n d : ℕ}
    (Ω : Opens (Fin n → ℝ)) (J : Opens (Fin d → ℝ))
    (X : Fin q → (Fin n → ℝ) → (Fin n → ℝ))
    (hX : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (X i) (Ω : Set (Fin n → ℝ)))
    (I : List (Fin q)) (v g : (Fin (n + d) → ℝ) → ℝ)
    (hg : hasIntrinsicWordDeriv (paddingNoDriftVectorFields (d := d) X) (P2.cylinder Ω J)
      (I.map (Fin.castAdd d)) v g)
    (z : Fin d → ℝ) (hz : z ∈ (J : Set (Fin d → ℝ))) :
    hasIntrinsicWordDeriv X Ω I (fun x => v (joinPoint x z)) (fun x => g (joinPoint x z)) := by
  have hfamily : paddingNoDriftVectorFields (d := d) X ∘ (Fin.castAdd d) =
      fun i => paddingBaseField (d := d) (X i) := by
    funext i
    exact paddingNoDriftVectorFields_original X i
  have h := (hasIntrinsicWordDeriv_map_indices_iff _ _ _ _ v g).mp hg
  rw [hfamily] at h
  exact hasIntrinsicWordDeriv_padding_slice Ω J X hX I v g h z hz

end RothschildStein.P1
