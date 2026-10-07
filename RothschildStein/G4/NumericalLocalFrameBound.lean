-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module
public import RothschildStein.G4.NumericalFrameCoefficientBound
public import RothschildStein.G4.NumericalRankBuffer
@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set Metric
namespace RothschildStein.G4

/-- Numerical rank and Cramer bounds on a common primitive-jet buffer. -/
theorem exists_numerical_local_frame_bound {k n s : ℕ} (w : Fin (k+1) → ℕ+)
    (M Δ R : ℝ) (hM : 0 ≤ M) (hΔ : 0 < Δ) (hR : 0 < R) :
    ∃ r C : ℝ, 0 < r ∧ r ≤ R/2 ∧ 0 < C ∧
      ∀ (Ω : Set (Fin n → ℝ)), IsOpen Ω →
      ∀ (X : Fin (k+1) → (Fin n → ℝ) → (Fin n → ℝ)),
      (∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (X i) Ω) →
      ∀ z : Fin n → ℝ, closedBall z R ⊆ Ω →
      (∀ i, HasJetBound Ω (closedBall z R) (X i) (1+s) M) →
      ∀ B : Fin n → ShortWord w s, Δ ≤ |frameDet (shortField w X) B z| →
      closedBall z r ⊆ Ω ∧
      (∀ y ∈ closedBall z r, frameDet (shortField w X) B y ≠ 0) ∧
      ∀ y ∈ closedBall z r, ∀ i (v : Fin n → ℝ),
        |frameCoefficient (shortField w X) B (fun _ => v) i y| ≤ C * ‖v‖ := by
  let P := wordJetBase n 1 s M ^ s
  have hP : 0 ≤ P := pow_nonneg (wordJetBase_nonneg_and_le hM).1 s
  obtain ⟨r,hr,hrR,hrank⟩ := exists_numerical_rank_buffer w M Δ R hM hΔ hR
  obtain ⟨C,hC,hcoef⟩ := exists_numerical_frame_coefficient_bound n P (Δ/2) hP (half_pos hΔ)
  refine ⟨r,C,hr,hrR,hC,?_⟩
  intro Ω hΩ X hX z hRΩ hjets B hB
  have hsub : closedBall z r ⊆ closedBall z R :=
    closedBall_subset_closedBall (hrR.trans (half_le_self hR.le))
  have hZ : ∀ I : ShortWord w s, ContDiffOn ℝ (⊤ : ℕ∞) (shortField w X I) Ω :=
    fun I => shortField_contDiffOn hΩ hX I
  have hjZ : ∀ I : ShortWord w s, HasJetBound Ω (closedBall z r) (shortField w X I) 0 P := by
    intro I j hj y hy
    exact mappedShortField_jet_bound hΩ hRΩ w X hX id hM hjets I j
      (hj.trans (by omega)) y (hsub hy)
  have hfloor : ∀ y ∈ closedBall z r, Δ/2 ≤ |frameDet (shortField w X) B y| :=
    hrank Ω hΩ X hX z hRΩ hjets B hB
  refine ⟨hsub.trans hRΩ,?_,?_⟩
  · intro y hy
    exact abs_pos.mp ((half_pos hΔ).trans_le (hfloor y hy))
  · exact hcoef (ShortWord w s) Ω (closedBall z r) hΩ (hsub.trans hRΩ)
      (shortField w X) hZ hjZ B hfloor
end RothschildStein.G4
