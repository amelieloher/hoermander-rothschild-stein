-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.P1.PaddingTestTransportDefs

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
open Set TopologicalSpace WithSeminorms
namespace RothschildStein.P1

/-- Coordinate transport on fixed compact support spaces. -/
def paddingSupportedToProductLM {n d : ℕ} {B : Type*}
    [NormedAddCommGroup B] [NormedSpace ℝ B]
    (K : Compacts (Fin (n + d) → ℝ)) :
    ContDiffMapSupportedIn (Fin (n + d) → ℝ) B ⊤ K →ₗ[ℝ]
      ContDiffMapSupportedIn ((Fin n → ℝ) × (Fin d → ℝ)) B ⊤
        (K.map (paddingCoordinates n d) (paddingCoordinates n d).continuous) where
  toFun φ :=
    { toFun p := φ ((paddingCoordinates n d).symm p)
      contDiff' := φ.contDiff.comp (paddingCoordinates n d).symm.contDiff
      zero_on_compl' := by
        intro p hp
        apply φ.zero_on_compl
        intro h
        exact hp ⟨(paddingCoordinates n d).symm p, h,
          (paddingCoordinates n d).apply_symm_apply p⟩ }
  map_add' _ _ := by ext; rfl
  map_smul' _ _ := by ext; rfl

/-- Every transported seminorm is bounded by the corresponding
original seminorm and a fixed power of the coordinate map norm. -/
theorem seminorm_paddingSupportedToProductLM_le {n d : ℕ} {B : Type*}
    [NormedAddCommGroup B] [NormedSpace ℝ B]
    (K : Compacts (Fin (n + d) → ℝ)) (i : ℕ)
    (φ : ContDiffMapSupportedIn (Fin (n + d) → ℝ) B ⊤ K) :
    ContDiffMapSupportedIn.seminorm ℝ ((Fin n → ℝ) × (Fin d → ℝ)) B ⊤
      (K.map (paddingCoordinates n d) (paddingCoordinates n d).continuous) i
        (paddingSupportedToProductLM K φ) ≤
      ‖paddingJoinCLM n d‖ ^ i *
        ContDiffMapSupportedIn.seminorm ℝ (Fin (n + d) → ℝ) B ⊤ K i φ := by
  apply (ContDiffMapSupportedIn.seminorm_top_le_iff ℝ
    (mul_nonneg (pow_nonneg (norm_nonneg _) _) (apply_nonneg _ _)) i _).mpr
  intro p _
  change ‖iteratedFDeriv ℝ i (φ ∘ paddingJoinCLM n d) p‖ ≤ _
  calc
    _ ≤ ‖iteratedFDeriv ℝ i φ (paddingJoinCLM n d p)‖ * ‖paddingJoinCLM n d‖ ^ i :=
      norm_iteratedFDeriv_paddingJoin_le φ.contDiff i p
    _ ≤ ContDiffMapSupportedIn.seminorm ℝ (Fin (n + d) → ℝ) B ⊤ K i φ *
        ‖paddingJoinCLM n d‖ ^ i := mul_le_mul_of_nonneg_right
          (ContDiffMapSupportedIn.norm_iteratedFDeriv_apply_le_seminorm_top ℝ)
          (pow_nonneg (norm_nonneg _) _)
    _ = _ := mul_comm _ _

/-- Fixed-support coordinate transport is continuous. -/
theorem continuous_paddingSupportedToProductLM {n d : ℕ} {B : Type*}
    [NormedAddCommGroup B] [NormedSpace ℝ B]
    (K : Compacts (Fin (n + d) → ℝ)) :
    Continuous (paddingSupportedToProductLM (B := B) K) := by
  apply continuous_of_isBounded
    (ContDiffMapSupportedIn.withSeminorms ℝ (Fin (n + d) → ℝ) B ⊤ K)
    (ContDiffMapSupportedIn.withSeminorms ℝ ((Fin n → ℝ) × (Fin d → ℝ)) B ⊤
      (K.map (paddingCoordinates n d) (paddingCoordinates n d).continuous)) _
    (.of_real fun i => ?_)
  exact ⟨{i}, ‖paddingJoinCLM n d‖ ^ i, fun φ => by
    simpa using seminorm_paddingSupportedToProductLM_le K i φ⟩

/-- The continuous coordinate transport on fixed supports. -/
def paddingSupportedToProductCLM {n d : ℕ} {B : Type*}
    [NormedAddCommGroup B] [NormedSpace ℝ B]
    (K : Compacts (Fin (n + d) → ℝ)) :
    ContDiffMapSupportedIn (Fin (n + d) → ℝ) B ⊤ K →L[ℝ]
      ContDiffMapSupportedIn ((Fin n → ℝ) × (Fin d → ℝ)) B ⊤
        (K.map (paddingCoordinates n d) (paddingCoordinates n d).continuous) where
  toLinearMap := paddingSupportedToProductLM K
  cont := continuous_paddingSupportedToProductLM K

end RothschildStein.P1
