-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module
public import RothschildStein.G4.NumericalConstantShortPrimitiveApproximation
public import RothschildStein.G4.NumericalControlledCurveBuffer
@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set Metric
open scoped ENNReal
namespace RothschildStein.G4
open G3 G1

/-- The actual constant-curve approximation has constants chosen from numerical
jet and value budgets before fields and buffers. Curve containment is derived
by the numerical first-exit bound. -/
theorem exists_numerical_constant_curve_approximation {m n s : ℕ} {w : Fin m → ℕ+}
    (D : FreeModelData m s w) (hs : 1 ≤ s) (hw : ∀ i, (w i : ℕ) ≤ s)
    (i₀ : Fin m) {r R B P : ℝ} (hr : 0 < r) (hR : 0 < R) (hB : 0 ≤ B) :
    ∃ C η M : ℝ, 0 < C ∧ 0 < η ∧ η ≤ 1 ∧ 0 < M ∧
      ∀ (Ω K : Set (Fin n → ℝ)), IsOpen Ω → ∀ z : Fin n → ℝ,
      (centreBuffer K r : Set (Fin n → ℝ)) ⊆ closedBall z R →
      K ⊆ closedBall z (R/2) → closedBall z R ⊆ Ω →
      ∀ X : Fin m → (Fin n → ℝ) → (Fin n → ℝ),
      (∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (X i) Ω) →
      CoordinateMultiIndexBudget (centreBuffer K r) X (4*(s+1)^3) B →
      (∀ j y, y ∈ closedBall z R → ‖shortField w X (shortIndex (s := s) w j) y‖ ≤ P) →
      ∀ δ : ℝ, δ < η → ∀ γ : ℝ → (Fin n → ℝ),
        IsConstantControlledCurve Ω
          (fun j => shortWeight w (shortIndex (s := s) w j))
          (fun j => shortField w X (shortIndex (s := s) w j)) δ γ →
        γ 0 ∈ K → ∃ y ∈ Ω,
          controlDistance Ω w X (γ 0) y ≤ ENNReal.ofReal (C * δ) ∧
          ‖y - γ 1‖ ≤ M * δ ^ (s + 1) := by
  obtain ⟨C,η,M,hC,hη,hη1,hM,ha⟩ :=
    exists_numerical_constant_short_primitive_approximation (n := n) (R := R) D hs hw i₀ hr hB
  obtain ⟨ε,hε,_hε1,hb⟩ := exists_numerical_controlled_curve_buffer
    (m := Fintype.card (ShortWord w s)) (n := n) R P hR
  refine ⟨C, min η ε, M, hC, lt_min hη hε,
    (min_le_left _ _).trans hη1, hM, ?_⟩
  intro Ω K hΩ z hbuffer hK hRΩ X hX hjets hval
  have hap := ha Ω K hΩ z hbuffer hRΩ X hX hjets
  have hbp := hb Ω (fun j => shortWeight w (shortIndex (s := s) w j))
    (fun j => shortField w X (shortIndex (s := s) w j)) z hval
  intro δ hδ γ hγ hx
  have hstay := hbp δ (hδ.trans_le (min_le_right _ _)) γ
    hγ.isControlledCurve (hK hx)
  obtain ⟨hδ0, hac, _hmap, a, hab, hd⟩ := hγ
  exact hap δ hδ0 (hδ.trans_le (min_le_left _ _)) a hab γ hac hstay hd hx
end RothschildStein.G4
