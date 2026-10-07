-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module
public import RothschildStein.L1.JointShortChartFamily
public import RothschildStein.L1.ProjectedFreePatch
@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set
namespace RothschildStein.L1

/-- The same fixed lift constructs actual original and lifted
joint families on compatible free patches, at every lifted center. -/
theorem FixedLiftData.nonempty_pairedJointShortChartFamilies {n k s m : ℕ}
    {w : Fin (k+1) → ℕ+} {Ω : Set (Fin n → ℝ)}
    {X : Fin (k+1) → (Fin n → ℝ) → (Fin n → ℝ)} {x₀ : Fin n → ℝ}
    (L : FixedLiftData w s Ω X x₀ m) (hn : 0 < n) (hs : 0 < s)
    (hΩ : IsOpen Ω) (hX : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (X i) Ω)
    {tO tl : ℝ} (htO : 0 < tO) (htO1 : tO < 1) (htl : 0 < tl) (htl1 : tl < 1)
    {ξ : Fin (n+m) → ℝ} (hξ : ξ ∈ L.U) :
    Nonempty (JointShortChartFamily (n := n) (s := s) w
      (basePoint '' (L.U : Set (Fin (n+m) → ℝ))) X (basePoint ξ) tO) ∧
    Nonempty (JointShortChartFamily (n := n+m) (s := s) w
      (L.U : Set (Fin (n+m) → ℝ)) (triangularLift X L.P) ξ tl) := by
  have hsub : basePoint '' (L.U : Set (Fin (n+m) → ℝ)) ⊆ Ω := by
    rintro y ⟨ζ,hζ,rfl⟩
    exact L.subset_domain hζ
  constructor
  · exact nonempty_jointShortChartFamily hn hs w htO htO1
      (isOpen_basePoint_image L.U.isOpen) X (fun i => (hX i).mono hsub)
      (L.original_bracketStepOn_image hΩ hX) ⟨ξ,hξ,rfl⟩
  · have hnm : 0 < n+m := lt_of_lt_of_le hn (Nat.le_add_right n m)
    exact nonempty_jointShortChartFamily hnm hs w htl htl1 L.U.isOpen
      (triangularLift X L.P) (fun i => (L.smooth i).mono L.subset_domain)
      (fun ζ hζ => (L.free_spanning ζ hζ).2) hξ

end RothschildStein.L1
