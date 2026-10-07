-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module
public import RothschildStein.L1.JointShiftedBallBox
public import RothschildStein.G4.ActualLocalFrameBuffer
@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set Metric Filter MeasureTheory
open scoped BigOperators Topology
namespace RothschildStein.L1
open G4

/-- Smooth local bracket generation constructs the strengthened
joint shifted chart family. The coefficient domain remains fixed while
the shift radius is chosen after the horizontal radius (BB pp. 520–521). -/
theorem exists_smooth_joint_shifted_short_ball_box {k n s : ℕ}
    (hn : 0 < n) (hs : 0 < s) (w : Fin (k+1) → ℕ+)
    {t : ℝ} (ht : 0 < t) (ht1 : t < 1)
    {Ω : Set (Fin n → ℝ)} (hΩ : IsOpen Ω)
    (X : Fin (k+1) → (Fin n → ℝ) → (Fin n → ℝ))
    (hX : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (X i) Ω)
    (hstep : bracketStepOn Ω w X s) {z : Fin n → ℝ} (hz : z ∈ Ω) :
    ∃ R M : ℝ, 0 < R ∧ 0 ≤ M ∧ closedBall z R ⊆ Ω ∧
    let m := Fintype.card (ShortWord w s)
    let wf : Fin m → ℕ+ := fun j => shortWeight w (shortIndex w j)
    let Zf : Fin m → (Fin n → ℝ) → (Fin n → ℝ) := fun j => shortField w X (shortIndex w j)
    let δ := R / (64 * (1 + ((n + m : ℕ) : ℝ) * wordJetBase n 0 s M ^ s))
    ∃ a₀ r₀ D κ : ℝ, 0 < a₀ ∧ a₀ < 1 ∧ a₀ < δ ∧ 0 < r₀ ∧ r₀ ≤ 1 ∧
      0 ≤ D ∧ 0 < κ ∧ (n : ℝ) * κ ≤ 1 / 4 ∧
      ∃ Φ : (Fin n → ShortWord w s) →
        (((Fin (n + m) → ℝ) × (Fin n → ℝ)) × ℝ) → (Fin n → ℝ),
      (∀ B, ContDiffOn ℝ (⊤ : ℕ∞) (Φ B)
        ((ball 0 δ ×ˢ ball z (R/4)) ×ˢ Ioo (-2) 2) ∧
        ∀ p ∈ ball 0 δ, ∀ x ∈ ball z (R/4), Φ B ((p,x),0) = x ∧
          ∀ τ ∈ Ioo (-2 : ℝ) 2, Φ B ((p,x),τ) ∈ ball z R ∧
            HasDerivAt (fun v => Φ B ((p,x),v))
              (∑ j, p j • shortField w X (selectedAuxiliaryIndex w B j) (Φ B ((p,x),τ))) τ) ∧
      ∀ a : ℝ, 0 < a → a ≤ a₀ →
      ∃ b : ℝ, 0 < b ∧ b < a/4 ∧ 2*b ≤ 1 ∧
      ∀ x ∈ closedBall z (R / 16), ∀ r : ℝ, 0 < r → r ≤ r₀ →
      ∀ B : Fin n → ShortWord w s,
        IsSuboptimal (shortField w X) (shortWeight w) B x t r →
      ∀ v ∈ weightedBox wf (b * r),
      let F := fun u => Φ B ((Fin.append u v, x), 1)
      let Q := weightedBox (shortWeight w ∘ B) (a * r)
      ChartAnalyticBounds Ω wf Zf ((Fintype.equivFin (ShortWord w s)) ∘ B) F Q r κ D ∧
      ChartTrajectories Ω Zf ((Fintype.equivFin (ShortWord w s)) ∘ B) F Q x v
        (fun u τ => Φ B ((Fin.append u v, x), τ)) ∧
      (v = 0 → F 0 = x) ∧ InjOn F Q ∧
      (∀ u ∈ Q, |frameDet (shortField w X) B x| / 4 ≤
        |Matrix.det (coordinateDerivativeMatrix (fderiv ℝ F u))| ∧
        |Matrix.det (coordinateDerivativeMatrix (fderiv ℝ F u))| ≤
          4 * |frameDet (shortField w X) B x|) ∧
      ({y | auxiliaryDistance (s := s) Ω w X x y < ENNReal.ofReal (b * r)} ⊆ F '' Q) ∧
      (F '' Q ⊆ {y | constantShortDistance (s := s) Ω w X x y < ENNReal.ofReal (2 * a * r)}) ∧
      ({y | constantShortDistance (s := s) Ω w X x y < ENNReal.ofReal (2 * a * r)} ⊆
        {y | auxiliaryDistance (s := s) Ω w X x y < ENNReal.ofReal (2 * a * r)}) ∧
      (v = 0 → F '' Q ⊆
        {y | constantShortDistance (s := s) Ω w X x y < ENNReal.ofReal (a * r)}) ∧
      IsOpen (F '' Q) ∧
      ∃ Ψ : (Fin n → ℝ) → (Fin n → ℝ), ContDiffOn ℝ (⊤ : ℕ∞) Ψ (F '' Q) ∧
        (∀ y ∈ F '' Q, Ψ y ∈ Q ∧ F (Ψ y) = y) ∧ (∀ u ∈ Q, Ψ (F u) = u) ∧
        ∀ y ∈ F '' Q, ∀ ℓ i : Fin n,
          |(fderiv ℝ Ψ y (shortField w X (B ℓ) y)) i| ≤ (4 / 3 : ℝ) *
            r ^ (((shortWeight w (B i) : ℕ) : ℤ) - ((shortWeight w (B ℓ) : ℕ) : ℤ)) := by
  let h := n*s+s
  let q := h-1
  have hh : 1 ≤ h := by dsimp [h]; omega
  have hq : q+1 = n*s+s := by dsimp [q,h] at *; omega
  obtain ⟨R,Δ,M,hR,hΔ,hM,hRΩ,hjets,hmax⟩ :=
    exists_actual_local_frame_buffer hΩ w X hX hstep
      (max (2*(n*s)+2*s) (max ((q+1)*s) (h+1+s))) hz
  refine ⟨R,M,hR,hM.le,hRΩ,?_⟩
  exact exists_joint_shifted_short_ball_box k n s h q hn hs hq (by omega)
    w hM.le hΔ hR ht ht1 Ω hΩ X hX hstep z hRΩ hjets hmax

end RothschildStein.L1
