-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module
public import RothschildStein.G4.SmoothConstantCurveApproximation
@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set Metric
open scoped ENNReal
namespace RothschildStein.G4
open G3 G1

/-- Small constant short-control balls have actual primitive reachable
approximants, with linear ordinary cost and an error of order s+1. -/
theorem exists_smooth_constant_ball_primitive_approximation {m n s : ℕ} {w : Fin m → ℕ+}
    (D : FreeModelData m s w) (hs : 1 ≤ s) (hw : ∀ i, (w i : ℕ) ≤ s)
    (i₀ : Fin m) {r R : ℝ} (hr : 0 < r) (hR : 0 < R)
    {Ω K : Set (Fin n → ℝ)} (hΩ : IsOpen Ω) {z : Fin n → ℝ}
    (hbuffer : (centreBuffer K r : Set (Fin n → ℝ)) ⊆ closedBall z R)
    (hK : K ⊆ closedBall z (R/2)) (hRΩ : closedBall z R ⊆ Ω)
    (X : Fin m → (Fin n → ℝ) → (Fin n → ℝ))
    (hX : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (X i) Ω) :
    ∃ C η M : ℝ, 0 < C ∧ 0 < η ∧ η ≤ 1 ∧ 0 < M ∧
      ∀ δ : ℝ, 0 < δ → δ < η → ∀ x ∈ K, ∀ y,
        constantShortDistance (s := s) Ω w X x y < ENNReal.ofReal δ →
        ∃ p ∈ Ω, controlDistance Ω w X x p ≤ ENNReal.ofReal (C * δ) ∧
          ‖p - y‖ ≤ M * δ ^ (s + 1) := by
  obtain ⟨C, η, M, hC, hη, hη1, hM, ha⟩ :=
    exists_smooth_constant_curve_approximation D hs hw i₀ hr hR
      hΩ hbuffer hK hRΩ X hX
  refine ⟨C, η, M, hC, hη, hη1, hM, ?_⟩
  intro δ hδ hδη x hx y hy
  obtain ⟨ε, hε, hεδ, γ, hγ, hzero, hone⟩ :=
    exists_constantCurve_of_distance_lt hy
  obtain ⟨p, hp, hcost, herr⟩ := ha ε (hεδ.trans hδη) γ hγ (by simpa only [hzero] using hx)
  refine ⟨p, hp, ?_, ?_⟩
  · simpa only [hzero] using hcost.trans
      (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left hεδ.le hC.le))
  · rw [hone] at herr
    exact herr.trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hε.le hεδ.le _) hM.le)
end RothschildStein.G4
