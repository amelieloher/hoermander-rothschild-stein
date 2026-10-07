-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module
public import RothschildStein.G4.ParameterPairedBallVolume
public import RothschildStein.G4.CompactParameterJetBudget
public import RothschildStein.G4.CompactParameterRankFloor
public import RothschildStein.G4.ContinuousShortFieldJets
@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set Metric MeasureTheory
open scoped BigOperators ENNReal
namespace RothschildStein.G4

/-- Smooth spatial coefficients with jointly continuous jets
construct a local paired volume provider uniform over compact parameters. -/
theorem exists_smooth_parameter_paired_ball_volume_provider {Sg : Type*}
    [UniformSpace Sg] [CompactSpace Sg] {k n s : ℕ}
    (hn : 0 < n) (hs : 0 < s) (w : Fin (k+1) → ℕ+) (hw : ∀ i, (w i : ℕ) ≤ s)
    {Ω : Set (Fin n → ℝ)} (hΩ : IsOpen Ω)
    (X : Sg → Fin (k+1) → (Fin n → ℝ) → (Fin n → ℝ))
    (hX : ∀ σ i, ContDiffOn ℝ (⊤ : ℕ∞) (X σ i) Ω)
    (hstep : ∀ σ, bracketStepOn Ω w (X σ) s)
    (hjoint : ∀ i j, ContinuousOn
      (fun q : Sg × (Fin n → ℝ) => iteratedFDeriv ℝ j (X q.1 i) q.2) (univ ×ˢ Ω))
    {z : Fin n → ℝ} (hz : z ∈ Ω) :
    let m := Fintype.card (ShortWord w s)
    let wf : Fin m → ℕ+ := fun j => shortWeight w (shortIndex w j)
    let Zf := fun σ j => shortField w (X σ) (shortIndex (s := s) w j)
    ∃ R c C ε : ℝ, 0 < R ∧ closedBall z R ⊆ Ω ∧ 0 < c ∧ 0 < C ∧ 0 < ε ∧
      ∀ σ, ∀ x ∈ closedBall z (R/16), ∀ r : ℝ, 0 < r → r ≤ ε →
        let Λ := volumePolynomial (fun B : Fin n → Fin m => frameDet (Zf σ) B x)
          (fun B => ∑ i, (wf (B i) : ℕ)) r
        (ENNReal.ofReal (c*Λ) ≤ volume (controlBall Ω w (X σ) x r) ∧
          volume (controlBall Ω w (X σ) x r) ≤ ENNReal.ofReal (C*Λ)) ∧
        (ENNReal.ofReal (c*Λ) ≤ volume (controlBall Ω wf (Zf σ) x r) ∧
          volume (controlBall Ω wf (Zf σ) x r) ≤ ENNReal.ofReal (C*Λ)) := by
  intro m wf Zf
  obtain ⟨d,hd,hball⟩ := Metric.isOpen_iff.mp hΩ z hz
  let R := d/2
  have hR : 0 < R := half_pos hd
  have hRΩ : closedBall z R ⊆ Ω := (closedBall_subset_ball (half_lt_self hd)).trans hball
  let h := n*s+s
  let q := h-1
  have horder : q+1 = n*s+s := by dsimp [q,h]; omega
  let H := max (max (2*(n*s)+2*s) (max ((q+1)*s) (h+1+s))) (max (4*(s+1)^3) (1+s))
  obtain ⟨M,hM,hjets⟩ := exists_compact_parameter_jet_budget hΩ
    (isCompact_closedBall z R) hRΩ X H (fun i j _ => hjoint i j)
  have hZjoint : ∀ I : ShortWord w s, ContinuousOn
      (fun q : Sg × (Fin n → ℝ) => shortField w (X q.1) I q.2) (univ ×ˢ closedBall z R) := by
    intro I
    exact (shortField_joint_continuity_of_spatial_jets hΩ w X
      (fun σ _ => hX σ) (fun i j _ => hjoint i j) I).1.mono
      (fun p hp => ⟨hp.1,hRΩ hp.2⟩)
  obtain ⟨Δ,hΔ,hmax⟩ := exists_compact_parameter_rank_floor
    (isCompact_closedBall z R) (fun σ => shortField w (X σ)) hZjoint
    (fun σ y hy => exists_short_frame (hstep σ) (hRΩ hy))
  obtain ⟨c,C,ε,hc,hC,hε,hvol⟩ := exists_parameter_paired_ball_volume_bounds k n s h q
    hn hs horder (by dsimp [q,h] at *; omega) w hw M Δ R hM.le hΔ hR Ω hΩ X hX hstep
    (fun i j _ => hjoint i j) z hRΩ hjets hmax (closedBall z (R/16))
    (isCompact_closedBall z (R/16)) (closedBall_subset_ball (by linarith))
  exact ⟨R,c,C,ε,hR,hRΩ,hc,hC,hε,hvol⟩
end RothschildStein.G4
