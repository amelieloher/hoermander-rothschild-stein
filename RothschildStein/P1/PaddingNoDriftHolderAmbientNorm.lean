-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.P1.PaddingIndexEmbedding

public import RothschildStein.P1.PaddingNoDriftHolderAmbientDescent
public import RothschildStein.Definitions.holderXENorm

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public section
noncomputable section
open Set TopologicalSpace
open scoped ENNReal BigOperators
namespace RothschildStein.P1

/-- Full quantitative Hölder descent at every order:
the intrinsic norm of a fixed slice is at most the
full padded norm, with constant one and including infinite values. -/
theorem holderXENorm_paddingNoDrift_ambient_slice_le {q n d k : ℕ}
    (Ω : Opens (Fin n → ℝ)) (JA : Opens (Fin d → ℝ))
    (V : Opens (Fin n → ℝ)) (J : Opens (Fin d → ℝ))
    (w : Fin q → ℕ+)
    (X : Fin q → (Fin n → ℝ) → (Fin n → ℝ))
    (hX : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (X i) (V : Set (Fin n → ℝ)))
    (α : ℝ) (v : (Fin (n + d) → ℝ) → ℝ)
    (z : Fin d → ℝ) (hzA : z ∈ (JA : Set (Fin d → ℝ)))
    (hz : z ∈ (J : Set (Fin d → ℝ))) :
    holderXENorm w X (controlDistance (Ω : Set (Fin n → ℝ)) w X) V k α
      (fun x => v (joinPoint x z)) ≤
    holderXENorm (paddingNoDriftWeights (d := d) w) (paddingNoDriftVectorFields (d := d) X)
      (controlDistance (P2.cylinder Ω JA : Set (Fin (n + d) → ℝ))
        (paddingNoDriftWeights (d := d) w) (paddingNoDriftVectorFields (d := d) X))
      (P2.cylinder V J) k α v := by
  classical
  have hword (I : List (Fin q)) :=
    intrinsicWordENorm_paddingNoDrift_ambient_slice_le Ω JA V J w X hX I α v z hzA hz
  have hinj : Function.Injective (List.map (Fin.castAdd d : Fin q → Fin (q + d))) :=
    List.map_injective_iff.mpr (Fin.castAdd_injective _ _)
  have hsub : (wordFamily w k).image (List.map (Fin.castAdd d)) ⊆
      wordFamily (paddingNoDriftWeights (d := d) w) k := by
    intro I hI
    obtain ⟨L, hL, rfl⟩ := Finset.mem_image.mp hI
    apply (S.mem_wordFamily_iff _ _ _).mpr
    rw [wordWeight_paddingNoDrift_map]
    exact (S.mem_wordFamily_iff _ _ _).mp hL
  simp only [holderXENorm]
  apply le_trans (Finset.sum_le_sum (fun I _ => hword I))
  have hsum :
      (∑ I ∈ (wordFamily w k).image (List.map (Fin.castAdd d)),
        intrinsicWordENorm (paddingNoDriftVectorFields (d := d) X)
          (controlDistance (P2.cylinder Ω JA : Set (Fin (n + d) → ℝ))
            (paddingNoDriftWeights (d := d) w) (paddingNoDriftVectorFields (d := d) X))
          (P2.cylinder V J) I α v) =
      ∑ I ∈ wordFamily w k,
        intrinsicWordENorm (paddingNoDriftVectorFields (d := d) X)
          (controlDistance (P2.cylinder Ω JA : Set (Fin (n + d) → ℝ))
            (paddingNoDriftWeights (d := d) w) (paddingNoDriftVectorFields (d := d) X))
          (P2.cylinder V J) (I.map (Fin.castAdd d)) α v :=
    Finset.sum_image (fun I _ L _ h => hinj h)
  rw [← hsum]
  apply Finset.sum_le_sum_of_subset_of_nonneg hsub
  intro I _ _
  exact bot_le


end RothschildStein.P1
