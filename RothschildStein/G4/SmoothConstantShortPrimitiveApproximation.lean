-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module
public import RothschildStein.G4.ConstantShortPrimitiveApproximation
public import RothschildStein.G4.CompactCoordinateJetBudget
@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set Metric MeasureTheory
open scoped ENNReal BigOperators
namespace RothschildStein.G4
open G3 G1

/-- Smoothness on a compact original-domain buffer supplies every coefficient
budget needed by the actual primitive approximation construction. -/
theorem exists_smooth_constant_short_primitive_approximation {m n s : ℕ} {w : Fin m → ℕ+}
    (D : FreeModelData m s w) (hs : 1 ≤ s) (hw : ∀ i, (w i : ℕ) ≤ s)
    (i₀ : Fin m) {r R : ℝ} (hr : 0 < r)
    {Ω K : Set (Fin n → ℝ)} (hΩ : IsOpen Ω) {z : Fin n → ℝ}
    (hbuffer : (centreBuffer K r : Set (Fin n → ℝ)) ⊆ closedBall z R)
    (hRΩ : closedBall z R ⊆ Ω)
    (X : Fin m → (Fin n → ℝ) → (Fin n → ℝ))
    (hX : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (X i) Ω) :
    ∃ C η M : ℝ, 0 < C ∧ 0 < η ∧ η ≤ 1 ∧ 0 < M ∧
      ∀ δ : ℝ, 0 < δ → δ < η →
      ∀ a : Fin (Fintype.card (ShortWord w s)) → ℝ,
        (∀ j, |a j| ≤ δ ^ (shortWeight w (shortIndex w j) : ℕ)) →
      ∀ γ : ℝ → (Fin n → ℝ), AbsolutelyContinuousOnInterval γ 0 1 →
        MapsTo γ (Icc 0 1) (closedBall z R) →
        (∀ᵐ t ∂(volume.restrict (Icc (0 : ℝ) 1)),
          HasDerivAt γ (∑ j, a j • shortField w X (shortIndex w j) (γ t)) t) →
        γ 0 ∈ K → ∃ y ∈ Ω,
          controlDistance Ω w X (γ 0) y ≤ ENNReal.ofReal (C * δ) ∧
          ‖y - γ 1‖ ≤ M * δ ^ (s + 1) := by
  obtain ⟨B, hB, hj⟩ := exists_compact_coordinate_jet_budget hΩ
    (isCompact_closedBall z R) hRΩ X hX (4 * (s + 1)^3)
  apply exists_constant_short_primitive_approximation D hs hw i₀ hr hB.le
    hΩ hbuffer hRΩ X hX
  intro x hx i k hk dirs hd j
  exact hj x (hbuffer hx) i k hk dirs hd j
end RothschildStein.G4
