-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.P1.PaddingHolderDescent
public import RothschildStein.P1.PaddingAmbientHolderSlice
public import RothschildStein.P1.PaddingIntrinsicSlice
public import RothschildStein.P1.IntrinsicWordReindex
public import RothschildStein.P1.PaddingWeightedSpan
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

/-- Intrinsic Hölder regularity of every order restricts from
the padded cylinder to the base, with the same word family `wordFamily`.
No passage through weak derivatives or extra representative premise is used. -/
theorem memHolderX_padding_ambient_slice {q n d k : ℕ}
    (Ω : Opens (Fin n → ℝ)) (JA : Opens (Fin d → ℝ))
    (V : Opens (Fin n → ℝ)) (J : Opens (Fin d → ℝ))
    (w : Fin (q + 1) → ℕ+)
    (X : Fin (q + 1) → (Fin n → ℝ) → (Fin n → ℝ))
    (hX : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (X i) (V : Set (Fin n → ℝ)))
    (α : ℝ) (v : (Fin (n + d) → ℝ) → ℝ)
    (hv : memHolderX (paddingControlWeights (d := d) w) (paddingVectorFields (d := d) X)
      (controlDistance (P2.cylinder Ω JA : Set (Fin (n + d) → ℝ))
        (paddingControlWeights (d := d) w) (paddingVectorFields (d := d) X))
      (P2.cylinder V J) k α v)
    (z : Fin d → ℝ) (hzA : z ∈ (JA : Set (Fin d → ℝ)))
    (hz : z ∈ (J : Set (Fin d → ℝ))) :
    memHolderX w X (controlDistance (Ω : Set (Fin n → ℝ)) w X) V k α
      (fun x => v (joinPoint x z)) := by
  refine ⟨(holderENorm_padding_ambient_slice_le Ω JA V J w X α v z hzA hz).trans_lt hv.1, ?_⟩
  intro I hI
  have hmap : I.map paddingGeneratorIndex ∈ wordFamily (paddingControlWeights (d := d) w) k := by
    apply (S.mem_wordFamily_iff _ _ _).mpr
    rw [wordWeight_padding_map]
    exact (S.mem_wordFamily_iff _ _ _).mp hI
  obtain ⟨g, hg, hgnorm⟩ := hv.2 _ hmap
  exact ⟨fun x => g (joinPoint x z),
    hasIntrinsicWordDeriv_padding_map_slice V J X hX I v g hg z hz,
    (holderENorm_padding_ambient_slice_le Ω JA V J w X α g z hzA hz).trans_lt hgnorm⟩

/-- Quantitative fixed-fiber descent for the infimum
norm of every intrinsic word; the constant is exactly one. -/
theorem intrinsicWordENorm_padding_ambient_slice_le {q n d : ℕ}
    (Ω : Opens (Fin n → ℝ)) (JA : Opens (Fin d → ℝ))
    (V : Opens (Fin n → ℝ)) (J : Opens (Fin d → ℝ))
    (w : Fin (q + 1) → ℕ+)
    (X : Fin (q + 1) → (Fin n → ℝ) → (Fin n → ℝ))
    (hX : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (X i) (V : Set (Fin n → ℝ)))
    (I : List (Fin (q + 1))) (α : ℝ) (v : (Fin (n + d) → ℝ) → ℝ)
    (z : Fin d → ℝ) (hzA : z ∈ (JA : Set (Fin d → ℝ)))
    (hz : z ∈ (J : Set (Fin d → ℝ))) :
    intrinsicWordENorm X (controlDistance (Ω : Set (Fin n → ℝ)) w X) V I α
      (fun x => v (joinPoint x z)) ≤
    intrinsicWordENorm (paddingVectorFields (d := d) X)
      (controlDistance (P2.cylinder Ω JA : Set (Fin (n + d) → ℝ))
        (paddingControlWeights (d := d) w) (paddingVectorFields (d := d) X))
      (P2.cylinder V J) (I.map paddingGeneratorIndex) α v := by
  unfold intrinsicWordENorm
  apply le_sInf
  rintro r ⟨g, hg, rfl⟩
  apply le_trans (sInf_le ?_) (holderENorm_padding_ambient_slice_le Ω JA V J w X α g z hzA hz)
  exact ⟨fun x => g (joinPoint x z),
    hasIntrinsicWordDeriv_padding_map_slice V J X hX I v g hg z hz, rfl⟩


end RothschildStein.P1
