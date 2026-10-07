-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.G4.TransportedBracket
public import RothschildStein.G1.MixedPartial

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set

namespace RothschildStein.G4

/-- The actual transported field is smooth in time on the open finite
trajectory overlap, by joint spatial derivative smoothness
(BB Lemma 9.48, pp. 442–443). -/
theorem localFlow_transported_contDiffOn_of_joint_contDiff
    {N : ℕ} {Ω U : Set (Fin N → ℝ)} (hU : IsOpen U)
    (Z Y : (Fin N → ℝ) → (Fin N → ℝ))
    (hY : ContDiffOn ℝ (⊤ : ℕ∞) Y Ω)
    {τ : ℝ} (Φ : ((Fin N → ℝ) × ℝ) → (Fin N → ℝ))
    (hjoint : ContDiffOn ℝ (⊤ : ℕ∞) Φ (U ×ˢ Ioo (-τ) τ))
    (hΦ : ∀ x ∈ U, Φ (x, 0) = x ∧ ∀ v ∈ Ioo (-τ) τ,
      HasDerivAt (fun w => Φ (x, w)) (Z (Φ (x, v))) v ∧ Φ (x, v) ∈ Ω)
    {x : Fin N → ℝ} (hx : x ∈ U) {T : Set ℝ}
    (hTτ : T ⊆ Ioo (-τ) τ) (hend : ∀ s ∈ T, Φ (x, -s) ∈ U) :
    ContDiffOn ℝ (⊤ : ℕ∞)
      (fun s => (fderiv ℝ (fun y => Φ (y, s)) (Φ (x, -s))) (Y (Φ (x, -s)))) T := by
  have hneg : ∀ s ∈ T, -s ∈ Ioo (-τ) τ := by
    intro s hs
    have ht := hTτ hs
    constructor <;> linarith [ht.1, ht.2]
  have hα : ContDiffOn ℝ (⊤ : ℕ∞) (fun s => Φ (x, -s)) T :=
    hjoint.comp (contDiffOn_const.prodMk contDiffOn_id.neg) (fun s hs => ⟨hx, hneg s hs⟩)
  have hJ := (RothschildStein.G1.spatial_derivative_contDiffOn hU hjoint).comp
    (hα.prodMk contDiffOn_id) (fun s hs => ⟨hend s hs, hTτ hs⟩)
  exact hJ.clm_apply (hY.comp hα (fun s hs => ((hΦ x hx).2 (-s) (hneg s hs)).2))

/-- An actual continuous local flow has smooth transported fields,
under joint smooth dependence of the flow (BB Lemma 9.48, pp. 442–443). -/
theorem localFlow_transported_contDiffOn
    {N : ℕ} {Ω U : Set (Fin N → ℝ)} (hΩ : IsOpen Ω) (hU : IsOpen U)
    (Z Y : (Fin N → ℝ) → (Fin N → ℝ))
    (hZ : ContDiffOn ℝ (⊤ : ℕ∞) Z Ω) (hY : ContDiffOn ℝ (⊤ : ℕ∞) Y Ω)
    {τ : ℝ} (hτ : 0 < τ) (Φ : ((Fin N → ℝ) × ℝ) → (Fin N → ℝ))
    (hc : ContinuousOn Φ (U ×ˢ Ioo (-τ) τ))
    (hΦ : ∀ x ∈ U, Φ (x, 0) = x ∧ ∀ v ∈ Ioo (-τ) τ,
      HasDerivAt (fun w => Φ (x, w)) (Z (Φ (x, v))) v ∧ Φ (x, v) ∈ Ω)
    {x : Fin N → ℝ} (hx : x ∈ U) {T : Set ℝ}
    (hTτ : T ⊆ Ioo (-τ) τ) (hend : ∀ s ∈ T, Φ (x, -s) ∈ U) :
    ContDiffOn ℝ (⊤ : ℕ∞)
      (fun s => (fderiv ℝ (fun y => Φ (y, s)) (Φ (x, -s))) (Y (Φ (x, -s)))) T := by
  have hjoint := RothschildStein.G1.local_flow_contDiffOn hΩ hU hτ hZ hc
    (fun y hy => (hΦ y hy).1) (fun y hy s hs =>
      ⟨((hΦ y hy).2 s hs).2, ((hΦ y hy).2 s hs).1⟩)
  exact localFlow_transported_contDiffOn_of_joint_contDiff hU Z Y hY Φ hjoint hΦ hx hTτ hend

end RothschildStein.G4
