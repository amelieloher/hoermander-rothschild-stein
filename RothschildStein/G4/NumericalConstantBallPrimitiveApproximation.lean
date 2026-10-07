-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module
public import RothschildStein.G4.NumericalConstantCurveApproximation
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
theorem exists_numerical_constant_ball_primitive_approximation {m n s : ℕ} {w : Fin m → ℕ+}
    (D : FreeModelData m s w) (hs : 1 ≤ s) (hw : ∀ i, (w i : ℕ) ≤ s)
    (i₀ : Fin m) {r R B P : ℝ} (hr : 0 < r) (hR : 0 < R) (hB : 0 ≤ B) :
    ∃ C η M : ℝ, 0 < C ∧ 0 < η ∧ η ≤ 1 ∧ 0 < M ∧
      ∀ (Ω K : Set (Fin n → ℝ)), IsOpen Ω → ∀ z : Fin n → ℝ,
      (centreBuffer K r : Set (Fin n → ℝ)) ⊆ closedBall z R →
      K ⊆ closedBall z (R/2) → closedBall z R ⊆ Ω →
      ∀ X : Fin m → (Fin n → ℝ) → (Fin n → ℝ),
      (∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (X i) Ω) →
      G3.CoordinateMultiIndexBudget (centreBuffer K r) X (4*(s+1)^3) B →
      (∀ j y, y ∈ closedBall z R → ‖shortField w X (shortIndex (s := s) w j) y‖ ≤ P) →
      ∀ δ : ℝ, 0 < δ → δ < η → ∀ x ∈ K, ∀ y,
        constantShortDistance (s := s) Ω w X x y < ENNReal.ofReal δ →
        ∃ p ∈ Ω, controlDistance Ω w X x p ≤ ENNReal.ofReal (C * δ) ∧
          ‖p - y‖ ≤ M * δ ^ (s + 1) := by
  obtain ⟨C,η,M,hC,hη,hη1,hM,ha⟩ :=
    exists_numerical_constant_curve_approximation (n := n) (P := P) D hs hw i₀ hr hR hB
  refine ⟨C, η, M, hC, hη, hη1, hM, ?_⟩
  intro Ω K hΩ z hbuffer hK hRΩ X hX hjets hval
  have hap := ha Ω K hΩ z hbuffer hK hRΩ X hX hjets hval
  intro δ hδ hδη x hx y hy
  obtain ⟨ε, hε, hεδ, γ, hγ, hzero, hone⟩ :=
    exists_constantCurve_of_distance_lt hy
  obtain ⟨p, hp, hcost, herr⟩ := hap ε (hεδ.trans hδη) γ hγ (by simpa only [hzero] using hx)
  refine ⟨p, hp, ?_, ?_⟩
  · simpa only [hzero] using hcost.trans
      (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left hεδ.le hC.le))
  · rw [hone] at herr
    exact herr.trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hε.le hεδ.le _) hM.le)
end RothschildStein.G4
