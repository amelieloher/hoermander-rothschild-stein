-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.S.SupportedHolderExtension

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
open Set TopologicalSpace
open scoped ENNReal
namespace RothschildStein.S
variable {n q : ℕ}

/-- The full Hölder norm also agrees on the supporting
ball and any larger ambient subset (BB Prop 2.18(iii), p. 85; covering adapter). -/
theorem holderENorm_eq_on_supported_ball
    (Ω : Opens (Fin n → ℝ)) (G : DistanceGeometry Ω)
    (w : Fin q → ℕ+) (X : Fin q → (Fin n → ℝ) → (Fin n → ℝ))
    (hG : G.d = controlDistance (Ω : Set (Fin n → ℝ)) w X)
    (hw : ∀ i,(w i : ℕ) ≤ 2) (x₀ : Ω) (R : ℝ≥0∞)
    {α : ℝ} (hα : 0 < α) (f : (Fin n → ℝ) → ℝ)
    {K V : Set (Fin n → ℝ)} (hK : IsCompact K)
    (hKB : K ⊆ {z | z ∈ (Ω : Set (Fin n → ℝ)) ∧ G.d x₀.val z < R})
    (hBV : {z | z ∈ (Ω : Set (Fin n → ℝ)) ∧ G.d x₀.val z < R} ⊆ V)
    (hVΩ : V ⊆ Ω) (hz : ∀ z ∈ V \ K,f z = 0) :
    holderENorm G.d α V f =
      holderENorm G.d α {z | z ∈ (Ω : Set (Fin n → ℝ)) ∧ G.d x₀.val z < R} f := by
  let B := {z | z ∈ (Ω : Set (Fin n → ℝ)) ∧ G.d x₀.val z < R}
  have hs : (⨆ z : V,ENNReal.ofReal |f z.val|) = ⨆ z : B,ENNReal.ofReal |f z.val| := by
    apply le_antisymm
    · apply iSup_le
      intro z
      by_cases hzB : z.val ∈ B
      · exact le_iSup_of_le ⟨z.val,hzB⟩ le_rfl
      · rw [hz z.val ⟨z.property,fun h => hzB (hKB h)⟩,abs_zero,ENNReal.ofReal_zero]
        exact zero_le
    · apply iSup_le
      intro z
      exact le_iSup_of_le ⟨z.val,hBV z.property⟩ le_rfl
  unfold holderENorm
  rw [hs,holderSeminorm_eq_on_supported_ball Ω G w X hG hw x₀ R hα f hK hKB hBV hVΩ hz]

end RothschildStein.S
