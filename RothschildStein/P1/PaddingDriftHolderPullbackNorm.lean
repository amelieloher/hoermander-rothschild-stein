-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.P1.PaddingDriftHolderLift
public import RothschildStein.P1.PaddingWordSum
public import RothschildStein.Definitions.holderXENorm

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public section
noncomputable section
open Set TopologicalSpace
open scoped ENNReal BigOperators
namespace RothschildStein.P1

/-- The full intrinsic Hölder norm of the forcing
pullback is bounded by the original norm with constant one, at every
order. Added-index words contribute exactly zero. -/
theorem holderXENorm_paddingDrift_pullback_le {q n d k : ℕ}
    (ΩA : Opens (Fin n → ℝ)) (JA : Opens (Fin d → ℝ))
    (Ω : Opens (Fin n → ℝ)) (J : Opens (Fin d → ℝ))
    (w : Fin (q + 1) → ℕ+) (X : Fin (q + 1) → (Fin n → ℝ) → (Fin n → ℝ))
    (hX : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (X i) (Ω : Set (Fin n → ℝ)))
    (α : ℝ) (hα : 0 ≤ α) (f : (Fin n → ℝ) → ℝ)
    (hf : memHolderX w X (controlDistance (ΩA : Set (Fin n → ℝ)) w X) Ω k α f) :
    holderXENorm (paddingControlWeights (d := d) w) (paddingVectorFields (d := d) X)
      (controlDistance (P2.cylinder ΩA JA : Set (Fin (n + d) → ℝ))
        (paddingControlWeights (d := d) w) (paddingVectorFields (d := d) X))
      (P2.cylinder Ω J) k α (fun ξ => f (basePoint ξ)) ≤
      holderXENorm w X (controlDistance (ΩA : Set (Fin n → ℝ)) w X) Ω k α f := by
  let D := controlDistance (ΩA : Set (Fin n → ℝ)) w X
  let DP := controlDistance (P2.cylinder ΩA JA : Set (Fin (n + d) → ℝ))
    (paddingControlWeights (d := d) w) (paddingVectorFields (d := d) X)
  have he : paddingDriftBaseAlphabet (d := d) X ∘ paddingGeneratorIndex = X := by
    funext i
    refine Fin.cases (by simp [paddingDriftBaseAlphabet, paddingGeneratorIndex])
      (fun j => by simp [paddingDriftBaseAlphabet, paddingGeneratorIndex]) i
  have hword (I : List (Fin (q + 1))) :
      intrinsicWordENorm (paddingVectorFields (d := d) X) DP (P2.cylinder Ω J)
        (I.map paddingGeneratorIndex) α (fun ξ => f (basePoint ξ)) ≤ intrinsicWordENorm X D Ω I α f := by
    unfold intrinsicWordENorm
    apply le_sInf
    rintro r ⟨g, hg, rfl⟩
    have hgb : hasIntrinsicWordDeriv (paddingDriftBaseAlphabet (d := d) X) Ω (I.map paddingGeneratorIndex) f g := by
      apply (hasIntrinsicWordDeriv_map_indices_iff _ _ _ _ _ _).mpr
      rw [he]
      exact hg
    have hgl := hasIntrinsicWordDeriv_paddingDrift_lift Ω J X hX _ f g hgb
    apply le_trans (sInf_le ?_) (holderENorm_paddingDrift_pullback_le ΩA JA Ω J w X α hα g)
    exact ⟨fun ξ => g (basePoint ξ), hgl, rfl⟩
  have hzero (I : List (Fin (q + d + 1)))
      (hI : I ∈ wordFamily (paddingControlWeights (d := d) w) k)
      (j : Fin d) (hj : (Fin.natAdd q j).succ ∈ I) :
      intrinsicWordENorm (paddingVectorFields (d := d) X) DP (P2.cylinder Ω J) I α
        (fun ξ => f (basePoint ξ)) = 0 := by
    have hgb := hasIntrinsicWordDeriv_paddingDriftBaseAlphabet_added Ω w X hX D α f hf I hI j hj
    have hgl := hasIntrinsicWordDeriv_paddingDrift_lift Ω J X hX I f (fun _ => 0) hgb
    apply le_antisymm ?_ bot_le
    unfold intrinsicWordENorm
    apply le_trans (sInf_le ?_) (le_of_eq (S.holderENorm_zero_function DP α (P2.cylinder Ω J : Set (Fin (n + d) → ℝ))))
    exact ⟨fun _ => 0, hgl, rfl⟩
  change (∑ I ∈ wordFamily (paddingControlWeights (d := d) w) k,
      intrinsicWordENorm (paddingVectorFields (d := d) X) DP (P2.cylinder Ω J) I α
        (fun ξ => f (basePoint ξ))) ≤ ∑ I ∈ wordFamily w k, intrinsicWordENorm X D Ω I α f
  rw [sum_paddingDrift_wordFamily w _ hzero]
  exact Finset.sum_le_sum (fun I _ => hword I)

end RothschildStein.P1
