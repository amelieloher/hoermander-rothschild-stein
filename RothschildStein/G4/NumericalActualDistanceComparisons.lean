-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module
public import RothschildStein.G4.NumericalOrdinaryAuxiliaryMetricComparison
public import RothschildStein.G4.NumericalConstantAuxiliaryMetricComparison
@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set Metric
open scoped ENNReal
namespace RothschildStein.G4

/-- Both actual distance comparisons have uniform numerical constants.
The free algebra model is constructed internally from the fixed weights. -/
theorem exists_numerical_actual_distance_comparisons (k n s h q : ℕ)
    (hn : 0 < n) (hs : 0 < s) (horder : q+1 = n*s+s) (hq : q+1 ≤ h)
    (w : Fin (k+1) → ℕ+)
    (hw : ∀ i, (w i : ℕ) ≤ s) (M Δ R₀ : ℝ) (hM : 0 ≤ M) (hΔ : 0 < Δ) (hR₀ : 0 < R₀) :
    ∃ R C_eq C_box ε : ℝ, 0 < R ∧ 0 < C_eq ∧ 0 < C_box ∧ 0 < ε ∧
      ∀ (Ω : Set (Fin n → ℝ)), IsOpen Ω →
      ∀ (X : Fin (k+1) → (Fin n → ℝ) → (Fin n → ℝ)),
      (∀ j, ContDiffOn ℝ (⊤ : ℕ∞) (X j) Ω) → bracketStepOn Ω w X s →
      ∀ x₀ : Fin n → ℝ, closedBall x₀ R₀ ⊆ Ω →
      (∀ j, HasJetBound Ω (closedBall x₀ R₀) (X j)
        (max (max (2*(n*s)+2*s) (max ((q+1)*s) (h+1+s)))
          (max (4*(s+1)^3) (1+s))) M) →
      (∀ y ∈ closedBall x₀ R₀, ∃ B : Fin n → ShortWord w s,
        Δ ≤ |frameDet (shortField w X) B y|) →
      closedBall x₀ R ⊆ Ω ∧
      ∀ x ∈ closedBall x₀ (R/2), ∀ y ∈ closedBall x₀ (R/2),
      auxiliaryDistance (s := s) Ω w X x y < ENNReal.ofReal ε →
      auxiliaryDistance (s := s) Ω w X x y ≤ controlDistance Ω w X x y ∧
      controlDistance Ω w X x y ≤ ENNReal.ofReal C_eq * auxiliaryDistance (s := s) Ω w X x y ∧
      auxiliaryDistance (s := s) Ω w X x y ≤ constantShortDistance (s := s) Ω w X x y ∧
      constantShortDistance (s := s) Ω w X x y ≤
        ENNReal.ofReal C_box * auxiliaryDistance (s := s) Ω w X x y := by
  let D := G3.freeModelData w (by omega : 0 < k+1) hw
  obtain ⟨R₁,C_eq,ε₁,hR₁,hC_eq,hε₁,hordinary⟩ :=
    exists_numerical_ordinary_auxiliary_metric_comparison k n s h q hn hs horder hq w D hw
      M Δ R₀ hM hΔ hR₀
  obtain ⟨C_box,ε₂,hC_box,hε₂,hbox⟩ :=
    exists_numerical_constant_auxiliary_metric_comparison k n s h q hn hs horder hq w
      M Δ R₀ hM hΔ hR₀
  let R := min R₁ (R₀/8)
  have hR : 0 < R := lt_min hR₁ (by positivity)
  refine ⟨R,C_eq,C_box,min ε₁ ε₂,hR,hC_eq,hC_box,lt_min hε₁ hε₂,?_⟩
  intro Ω hΩ X hX hstep z hRΩ hjets hmax
  obtain ⟨hR₁Ω,heq⟩ := hordinary Ω hΩ X hX hstep z hRΩ hjets hmax
  refine ⟨(closedBall_subset_closedBall (min_le_left _ _)).trans hR₁Ω,?_⟩
  intro x hx y hy hd
  have hx₁ : x ∈ closedBall z (R₁/2) :=
    closedBall_subset_closedBall (by dsimp [R]; linarith [min_le_left R₁ (R₀/8)]) hx
  have hy₁ : y ∈ closedBall z (R₁/2) :=
    closedBall_subset_closedBall (by dsimp [R]; linarith [min_le_left R₁ (R₀/8)]) hy
  have hx₂ : x ∈ ball z (R₀/8) :=
    closedBall_subset_ball (by dsimp [R]; linarith [min_le_right R₁ (R₀/8)]) hx
  have he := heq x hx₁ y hy₁ (hd.trans_le (ENNReal.ofReal_le_ofReal (min_le_left _ _)))
  have hb := hbox Ω hΩ X hX hstep z hRΩ
    (fun i => (hjets i).mono (le_max_left _ _)) hmax x hx₂ y
    (hd.trans_le (ENNReal.ofReal_le_ofReal (min_le_right _ _)))
  exact ⟨he.1,he.2,hb.1,hb.2⟩
end RothschildStein.G4
