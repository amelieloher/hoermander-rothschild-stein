-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module
public import RothschildStein.G4.SmoothConstantBallPrimitiveApproximation
public import RothschildStein.G4.SmoothConstantBallSandwich
@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set Metric
open scoped ENNReal
namespace RothschildStein.G4
open G3 G1

/-- Every sufficiently small auxiliary endpoint has an actual
primitive reachable approximant. The linear ordinary cost and higher-order
Euclidean error follow from the constructed ball-box charts and finite Lie flows. -/
theorem exists_smooth_auxiliary_primitive_approximation {k n s : ℕ}
    (hn : 0 < n) (hs : 1 ≤ s) (w : Fin (k+1) → ℕ+)
    (D : FreeModelData (k+1) s w) (hw : ∀ i, (w i : ℕ) ≤ s)
    {Ω : Set (Fin n → ℝ)} (hΩ : IsOpen Ω)
    (X : Fin (k+1) → (Fin n → ℝ) → (Fin n → ℝ))
    (hX : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (X i) Ω)
    (hstep : bracketStepOn Ω w X s) {z : Fin n → ℝ} (hz : z ∈ Ω) :
    ∃ R C η M : ℝ, 0 < R ∧ closedBall z R ⊆ Ω ∧
      0 < C ∧ 0 < η ∧ 0 < M ∧
      ∀ x ∈ closedBall z (R/16), ∀ δ : ℝ, 0 < δ → δ < η → ∀ y,
        auxiliaryDistance (s := s) Ω w X x y < ENNReal.ofReal δ →
        ∃ p ∈ Ω, controlDistance Ω w X x p ≤ ENNReal.ofReal (C*δ) ∧
          ‖p-y‖ ≤ M*δ^(s+1) := by
  obtain ⟨R, A, ρ, hR, hRΩ, hA, hρ, hball⟩ :=
    exists_smooth_constant_ball_sandwich hn (by omega) w hΩ X hX hstep hz
  have hbuffer : (centreBuffer (closedBall z (R/16)) (R/16) : Set (Fin n → ℝ)) ⊆
      closedBall z R := by
    intro y hy
    obtain ⟨x, hx, hyx⟩ := mem_centreBuffer_iff.mp hy
    rw [mem_closedBall] at hx ⊢
    rw [mem_ball] at hyx
    have hh := dist_triangle y x z
    linarith
  have hhalf : closedBall z (R/16) ⊆ closedBall z (R/2) :=
    closedBall_subset_closedBall (by linarith)
  obtain ⟨C, η, M, hC, hη, _hη1, hM, happrox⟩ :=
    exists_smooth_constant_ball_primitive_approximation D hs hw (0 : Fin (k+1))
      (by positivity : 0 < R/16) hR hΩ hbuffer hhalf hRΩ X hX
  refine ⟨R, C*A, min ρ (η/A), M*A^(s+1), hR, hRΩ,
    mul_pos hC hA, lt_min hρ (div_pos hη hA), mul_pos hM (pow_pos hA _), ?_⟩
  intro x hx δ hδ hδη y hy
  have hδρ : δ ≤ ρ := hδη.le.trans (min_le_left _ _)
  have hAδη : A*δ < η := by
    have hh := (lt_div_iff₀ hA).mp (hδη.trans_le (min_le_right _ _))
    nlinarith
  have hyc := hball x hx δ hδ hδρ hy
  obtain ⟨p, hp, hcost, herr⟩ := happrox (A*δ) (mul_pos hA hδ) hAδη x hx y hyc
  refine ⟨p, hp, ?_, ?_⟩
  · simpa only [mul_assoc] using hcost
  · simpa only [mul_pow, mul_assoc] using herr
end RothschildStein.G4
