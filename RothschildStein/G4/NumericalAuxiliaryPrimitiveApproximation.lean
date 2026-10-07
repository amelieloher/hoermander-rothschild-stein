-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module
public import RothschildStein.G4.NumericalConstantShortBallSandwich
public import RothschildStein.G4.NumericalConstantBallPrimitiveApproximation
public import RothschildStein.G4.CoordinateJetBudgetOfJetBound
public import RothschildStein.G4.MappedShortFieldBudget
@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set Metric
open scoped ENNReal
namespace RothschildStein.G4

/-- Numerical primitive endpoint approximation for actual auxiliary balls.
All constants precede the domain and fields. -/
theorem exists_numerical_auxiliary_primitive_approximation (k n s h q : ℕ)
    (hn : 0 < n) (hs : 0 < s) (horder : q+1 = n*s+s) (hq : q+1 ≤ h)
    (w : Fin (k+1) → ℕ+) (D : G3.FreeModelData (k+1) s w)
    (hw : ∀ i, (w i : ℕ) ≤ s) (M Δ R : ℝ) (hM : 0 ≤ M) (hΔ : 0 < Δ) (hR : 0 < R) :
    ∃ C η E : ℝ, 0 < C ∧ 0 < η ∧ 0 < E ∧
      ∀ (Ω : Set (Fin n → ℝ)), IsOpen Ω →
      ∀ (X : Fin (k+1) → (Fin n → ℝ) → (Fin n → ℝ)),
      (∀ j, ContDiffOn ℝ (⊤ : ℕ∞) (X j) Ω) → bracketStepOn Ω w X s →
      ∀ x₀ : Fin n → ℝ, closedBall x₀ R ⊆ Ω →
      (∀ j, HasJetBound Ω (closedBall x₀ R) (X j)
        (max (max (2*(n*s)+2*s) (max ((q+1)*s) (h+1+s)))
          (max (4*(s+1)^3) (1+s))) M) →
      (∀ y ∈ closedBall x₀ R, ∃ B : Fin n → ShortWord w s,
        Δ ≤ |frameDet (shortField w X) B y|) →
      ∀ x ∈ closedBall x₀ (R/16), ∀ δ : ℝ, 0 < δ → δ < η → ∀ y,
        auxiliaryDistance (s := s) Ω w X x y < ENNReal.ofReal δ →
        ∃ p ∈ Ω, controlDistance Ω w X x p ≤ ENNReal.ofReal (C*δ) ∧
          ‖p-y‖ ≤ E*δ^(s+1) := by
  obtain ⟨A,ρ,hA,hρ,hball⟩ :=
    exists_numerical_constant_short_ball_sandwich k n s h q hn hs horder hq w M Δ R hM hΔ hR
  let P := wordJetBase n 1 s M ^ s
  obtain ⟨C,η,E,hC,hη,_hη1,hE,happrox⟩ :=
    exists_numerical_constant_ball_primitive_approximation (n := n) (r := R/16) (R := R)
      (B := M) (P := P) D (by omega) hw (0 : Fin (k+1)) (by positivity) hR hM
  refine ⟨C*A,min ρ (η/A),E*A^(s+1),mul_pos hC hA,
    lt_min hρ (div_pos hη hA),mul_pos hE (pow_pos hA _),?_⟩
  intro Ω hΩ X hX hstep z hRΩ hjets hmax
  have hbuffer : (G3.centreBuffer (closedBall z (R/16)) (R/16) : Set (Fin n → ℝ)) ⊆
      closedBall z R := by
    intro y hy
    obtain ⟨x,hx,hyx⟩ := G3.mem_centreBuffer_iff.mp hy
    rw [mem_closedBall] at hx ⊢
    rw [mem_ball] at hyx
    have hh := dist_triangle y x z
    linarith
  have hjc : ∀ i, HasJetBound Ω (G3.centreBuffer (closedBall z (R/16)) (R/16))
      (X i) (4*(s+1)^3) M := by
    intro i j hj y hy
    exact hjets i j (hj.trans ((le_max_left _ _).trans (le_max_right _ _))) y (hbuffer hy)
  have hshort : ∀ i, HasJetBound Ω (closedBall z R) (X i) (1+s) M :=
    fun i => (hjets i).mono ((le_max_right _ _).trans (le_max_right _ _))
  have hval : ∀ j y, y ∈ closedBall z R →
      ‖shortField w X (shortIndex (s := s) w j) y‖ ≤ P := by
    intro j y hy
    have hb := mappedShortField_jet_bound hΩ hRΩ w X hX id hM hshort
      (shortIndex (s := s) w j) 0 (by omega) y hy
    simpa only [norm_iteratedFDerivWithin_zero,id_eq,P] using hb
  have hap := happrox Ω (closedBall z (R/16)) hΩ z hbuffer
    (closedBall_subset_closedBall (by linarith : R/16 ≤ R/2)) hRΩ X hX
    (coordinate_jet_budget_of_jet_bound hΩ (hbuffer.trans hRΩ) X hX hjc) hval
  intro x hx δ hδ hδη y hy
  have hx' : x ∈ ball z (R/8) := by
    exact closedBall_subset_ball (by linarith : R/16 < R/8) hx
  have hδρ : δ ≤ ρ := hδη.le.trans (min_le_left _ _)
  have hAδη : A*δ < η := by
    have hh := (lt_div_iff₀ hA).mp (hδη.trans_le (min_le_right _ _))
    nlinarith
  have hyc := hball Ω hΩ X hX hstep z hRΩ
    (fun i => (hjets i).mono (le_max_left _ _)) hmax x hx' δ hδ hδρ hy
  obtain ⟨p,hp,hcost,herr⟩ := hap (A*δ) (mul_pos hA hδ) hAδη x hx y hyc
  refine ⟨p,hp,?_,?_⟩
  · simpa only [mul_assoc] using hcost
  · simpa only [mul_pow,mul_assoc] using herr
end RothschildStein.G4
