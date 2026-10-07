-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module
public import RothschildStein.G4.SmoothConstantShortPrimitiveApproximation
public import RothschildStein.G4.CompactControlledCurveBuffer
@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set Metric
open scoped ENNReal
namespace RothschildStein.G4
open G3 G1

/-- The actual constant-curve approximation requires only smooth original
coefficients and geometric buffers. Compact jets and curve containment
are derived internally. -/
theorem exists_smooth_constant_curve_approximation {m n s : ℕ} {w : Fin m → ℕ+}
    (D : FreeModelData m s w) (hs : 1 ≤ s) (hw : ∀ i, (w i : ℕ) ≤ s)
    (i₀ : Fin m) {r R : ℝ} (hr : 0 < r) (hR : 0 < R)
    {Ω K : Set (Fin n → ℝ)} (hΩ : IsOpen Ω) {z : Fin n → ℝ}
    (hbuffer : (centreBuffer K r : Set (Fin n → ℝ)) ⊆ closedBall z R)
    (hK : K ⊆ closedBall z (R/2)) (hRΩ : closedBall z R ⊆ Ω)
    (X : Fin m → (Fin n → ℝ) → (Fin n → ℝ))
    (hX : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (X i) Ω) :
    ∃ C η M : ℝ, 0 < C ∧ 0 < η ∧ η ≤ 1 ∧ 0 < M ∧
      ∀ δ : ℝ, δ < η → ∀ γ : ℝ → (Fin n → ℝ),
        IsConstantControlledCurve Ω
          (fun j => shortWeight w (shortIndex (s := s) w j))
          (fun j => shortField w X (shortIndex (s := s) w j)) δ γ →
        γ 0 ∈ K → ∃ y ∈ Ω,
          controlDistance Ω w X (γ 0) y ≤ ENNReal.ofReal (C * δ) ∧
          ‖y - γ 1‖ ≤ M * δ ^ (s + 1) := by
  obtain ⟨C, η, M, hC, hη, hη1, hM, ha⟩ :=
    exists_smooth_constant_short_primitive_approximation D hs hw i₀ hr
      hΩ hbuffer hRΩ X hX
  obtain ⟨ε, hε, _hε1, hb⟩ := exists_compact_controlled_curve_buffer
    (Ω := Ω) (fun j => shortWeight w (shortIndex (s := s) w j))
    (fun j => shortField w X (shortIndex (s := s) w j)) hR
    (fun j => (shortField_contDiffOn hΩ hX _).continuousOn.mono hRΩ)
  refine ⟨C, min η ε, M, hC, lt_min hη hε,
    (min_le_left _ _).trans hη1, hM, ?_⟩
  intro δ hδ γ hγ hx
  have hstay := hb δ (hδ.trans_le (min_le_right _ _)) γ
    hγ.isControlledCurve (hK hx)
  obtain ⟨hδ0, hac, _hmap, a, hab, hd⟩ := hγ
  exact ha δ hδ0 (hδ.trans_le (min_le_left _ _)) a hab γ hac hstay hd hx
end RothschildStein.G4
