-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module
public import RothschildStein.G4.NumericalActualDistanceComparisonsFullBall
@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set Metric
open scoped ENNReal
namespace RothschildStein.G4

/-- One numerical set of distance constants works at every center
whose primitive jets and short-frame ranks satisfy the common buffer budgets.
In particular the constants are uniform across coefficient parameter families. -/
theorem exists_numerical_uniform_distance_comparisons (k n s h q : ℕ)
    (hn : 0 < n) (hs : 0 < s) (horder : q+1 = n*s+s) (hq : q+1 ≤ h)
    (w : Fin (k+1) → ℕ+)
    (hw : ∀ i, (w i : ℕ) ≤ s) (M Δ R₀ : ℝ) (hM : 0 ≤ M) (hΔ : 0 < Δ) (hR₀ : 0 < R₀) :
    ∃ C_eq C_box ε : ℝ, 0 < C_eq ∧ 0 < C_box ∧ 0 < ε ∧
      ∀ (Ω : Set (Fin n → ℝ)), IsOpen Ω →
      ∀ (X : Fin (k+1) → (Fin n → ℝ) → (Fin n → ℝ)),
      (∀ j, ContDiffOn ℝ (⊤ : ℕ∞) (X j) Ω) → bracketStepOn Ω w X s →
      ∀ x₀ : Fin n → ℝ, closedBall x₀ R₀ ⊆ Ω →
      (∀ j, HasJetBound Ω (closedBall x₀ R₀) (X j)
        (max (max (2*(n*s)+2*s) (max ((q+1)*s) (h+1+s)))
          (max (4*(s+1)^3) (1+s))) M) →
      (∀ y ∈ closedBall x₀ R₀, ∃ B : Fin n → ShortWord w s,
        Δ ≤ |frameDet (shortField w X) B y|) →
      ∀ y,
      auxiliaryDistance (s := s) Ω w X x₀ y < ENNReal.ofReal ε →
      auxiliaryDistance (s := s) Ω w X x₀ y ≤ controlDistance Ω w X x₀ y ∧
      controlDistance Ω w X x₀ y ≤ ENNReal.ofReal C_eq * auxiliaryDistance (s := s) Ω w X x₀ y ∧
      auxiliaryDistance (s := s) Ω w X x₀ y ≤ constantShortDistance (s := s) Ω w X x₀ y ∧
      constantShortDistance (s := s) Ω w X x₀ y ≤
        ENNReal.ofReal C_box * auxiliaryDistance (s := s) Ω w X x₀ y := by
  obtain ⟨R,C_eq,C_box,ε,hR,hC_eq,hC_box,hε,hprovider⟩ :=
    exists_numerical_actual_distance_comparisons_full_ball k n s h q hn hs horder hq w hw
      M Δ R₀ hM hΔ hR₀
  refine ⟨C_eq,C_box,ε,hC_eq,hC_box,hε,?_⟩
  intro Ω hΩ X hX hstep z hRΩ hjets hmax y hd
  exact (hprovider Ω hΩ X hX hstep z hRΩ hjets hmax).2 z
    (mem_closedBall_self (by positivity)) y hd
end RothschildStein.G4
