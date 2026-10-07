-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.G4.ActualLocalFrameBuffer
public import RothschildStein.G4.ActualShortBallBox

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set Metric Filter MeasureTheory
open scoped BigOperators Topology
namespace RothschildStein.G4

/-- The complete actual shifted ball-box package locally
from smoothness and the bracket-step hypothesis. All rank and finite
jet bounds are constructed on an original-domain buffer. The chart,
Jacobian, inverse and ball inclusions belong to the same flow family
(BB Theorems 9.11/9.42 and Proposition 9.52). -/
theorem exists_smooth_short_ball_box_provider {k n s : ℕ}
    (hn : 0 < n) (hs : 0 < s) (w : Fin (k + 1) → ℕ+)
    {t : ℝ} (ht : 0 < t) (ht1 : t < 1)
    {Ω : Set (Fin n → ℝ)} (hΩ : IsOpen Ω)
    (X : Fin (k + 1) → (Fin n → ℝ) → (Fin n → ℝ))
    (hX : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (X i) Ω)
    (hstep : bracketStepOn Ω w X s) {z : Fin n → ℝ} (hz : z ∈ Ω) :
    ∃ R : ℝ, 0 < R ∧ closedBall z R ⊆ Ω ∧
    let m := Fintype.card (ShortWord w s)
    let wf : Fin m → ℕ+ := fun j => shortWeight w (shortIndex w j)
    let Zf : Fin m → (Fin n → ℝ) → (Fin n → ℝ) := fun j => shortField w X (shortIndex w j)
    ∃ a b r₀ D κ : ℝ, 0 < a ∧ a < 1 ∧ 0 < b ∧ b < a / 4 ∧ 2 * b ≤ 1 ∧ 0 < r₀ ∧ r₀ ≤ 1 ∧
      0 ≤ D ∧ 0 < κ ∧ (n : ℝ) * κ ≤ 1 / 4 ∧
      ∃ Φ : (Fin n → ShortWord w s) →
        (((Fin (n + m) → ℝ) × (Fin n → ℝ)) × ℝ) → (Fin n → ℝ),
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
  let h := n * s + s
  let q := h - 1
  have hh : 1 ≤ h := by dsimp [h]; omega
  have hq : q + 1 = n * s + s := by dsimp [q, h] at *; omega
  obtain ⟨R, Δ, M, hR, hΔ, hM, hRΩ, hjets, hmax⟩ :=
    exists_actual_local_frame_buffer hΩ w X hX hstep
      (max (2 * (n * s) + 2 * s) (max ((q + 1) * s) (h + 1 + s))) hz
  refine ⟨R, hR, hRΩ, ?_⟩
  exact exists_actual_short_ball_box k n s h q hn hs hq (by omega)
    w hM.le hΔ hR ht ht1 Ω hΩ X hX hstep z hRΩ hjets hmax

end RothschildStein.G4
