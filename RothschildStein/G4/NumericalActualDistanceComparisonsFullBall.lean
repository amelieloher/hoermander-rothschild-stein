-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module
public import RothschildStein.G4.NumericalActualDistanceComparisons
public import RothschildStein.G4.NumericalControlledCurveBuffer
public import RothschildStein.G4.MappedShortFieldBudget
@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set Metric
open scoped ENNReal
namespace RothschildStein.G4

/-- The numerical comparisons hold for every sufficiently close auxiliary
endpoint in the original domain, with no endpoint patch premise. -/
theorem exists_numerical_actual_distance_comparisons_full_ball (k n s h q : ℕ)
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
      ∀ x ∈ closedBall x₀ (R/4), ∀ y,
      auxiliaryDistance (s := s) Ω w X x y < ENNReal.ofReal ε →
      auxiliaryDistance (s := s) Ω w X x y ≤ controlDistance Ω w X x y ∧
      controlDistance Ω w X x y ≤ ENNReal.ofReal C_eq * auxiliaryDistance (s := s) Ω w X x y ∧
      auxiliaryDistance (s := s) Ω w X x y ≤ constantShortDistance (s := s) Ω w X x y ∧
      constantShortDistance (s := s) Ω w X x y ≤
        ENNReal.ofReal C_box * auxiliaryDistance (s := s) Ω w X x y := by
  obtain ⟨R₁,C_eq,C_box,ε₁,hR₁,hC_eq,hC_box,hε₁,hprovider⟩ :=
    exists_numerical_actual_distance_comparisons k n s h q hn hs horder hq w hw
      M Δ R₀ hM hΔ hR₀
  let R := min R₁ (R₀/8)
  have hR : 0 < R := lt_min hR₁ (by positivity)
  let P := wordJetBase n 1 s M ^ s
  obtain ⟨η,hη,_hη1,hstay⟩ := exists_numerical_controlled_curve_buffer
    (m := Fintype.card (ShortWord w s)) (n := n) (R/2) P (by positivity)
  refine ⟨R,C_eq,C_box,min ε₁ η,hR,hC_eq,hC_box,lt_min hε₁ hη,?_⟩
  intro Ω hΩ X hX hstep z hRΩ hjets hmax
  obtain ⟨hR₁Ω,hcomp⟩ := hprovider Ω hΩ X hX hstep z hRΩ hjets hmax
  have hRR₁ : R ≤ R₁ := min_le_left _ _
  have hRR₀ : R/2 ≤ R₀ := by dsimp [R]; linarith [min_le_right R₁ (R₀/8)]
  have hjshort : ∀ i, HasJetBound Ω (closedBall z R₀) (X i) (1+s) M :=
    fun i => (hjets i).mono ((le_max_right _ _).trans (le_max_right _ _))
  have hval : ∀ j y, y ∈ closedBall z (R/2) →
      ‖shortField w X (shortIndex (s := s) w j) y‖ ≤ P := by
    intro j y hy
    have hb := mappedShortField_jet_bound hΩ hRΩ w X hX id hM hjshort
      (shortIndex (s := s) w j) 0 (by omega) y (closedBall_subset_closedBall hRR₀ hy)
    simpa only [norm_iteratedFDerivWithin_zero,id_eq,P] using hb
  refine ⟨(closedBall_subset_closedBall hRR₁).trans hR₁Ω,?_⟩
  intro x hx y hd
  obtain ⟨δ,hδ,hδsmall,γ,hγ,hzero,hone⟩ :=
    G1.exists_controlledCurve_of_controlDistance_lt hd
  have hγstay := hstay Ω (fun j => shortWeight w (shortIndex (s := s) w j))
    (fun j => shortField w X (shortIndex (s := s) w j)) z hval δ
    (hδsmall.trans_le (min_le_right _ _)) γ hγ
    (by simpa only [hzero,show R/2/2 = R/4 by ring] using hx)
  have hy : y ∈ closedBall z (R/2) := by
    simpa only [hone] using hγstay (show (1 : ℝ) ∈ Icc 0 1 by constructor <;> norm_num)
  have hx' : x ∈ closedBall z (R₁/2) :=
    closedBall_subset_closedBall (by linarith) hx
  have hy' : y ∈ closedBall z (R₁/2) :=
    closedBall_subset_closedBall (by linarith) hy
  exact hcomp x hx' y hy' (hd.trans_le (ENNReal.ofReal_le_ofReal (min_le_left _ _)))
end RothschildStein.G4
