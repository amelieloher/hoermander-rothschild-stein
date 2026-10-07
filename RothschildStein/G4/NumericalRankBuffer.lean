-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module
public import RothschildStein.G4.FrameDetJetBounds
public import RothschildStein.G4.MappedShortFieldBudget
public import Mathlib.Analysis.Calculus.MeanValue
@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set Metric
namespace RothschildStein.G4

/-- Primitive finite jets give a numerical rank
buffer: a frame of determinant at least Δ at the center retains at least
Δ/2 throughout the smaller ball. The radius precedes all fields. -/
theorem exists_numerical_rank_buffer {k n s : ℕ} (w : Fin (k+1) → ℕ+)
    (M Δ R : ℝ) (hM : 0 ≤ M) (hΔ : 0 < Δ) (hR : 0 < R) :
    ∃ r : ℝ, 0 < r ∧ r ≤ R/2 ∧
      ∀ (Ω : Set (Fin n → ℝ)), IsOpen Ω →
      ∀ (X : Fin (k+1) → (Fin n → ℝ) → (Fin n → ℝ)),
      (∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (X i) Ω) →
      ∀ z : Fin n → ℝ, closedBall z R ⊆ Ω →
      (∀ i, HasJetBound Ω (closedBall z R) (X i) (1+s) M) →
      ∀ B : Fin n → ShortWord w s, Δ ≤ |frameDet (shortField w X) B z| →
      ∀ y ∈ closedBall z r, Δ/2 ≤ |frameDet (shortField w X) B y| := by
  let P := wordJetBase n 1 s M ^ s
  have hP : 0 ≤ P := pow_nonneg (wordJetBase_nonneg_and_le hM).1 s
  obtain ⟨L,hL,hdet⟩ := exists_frameDet_jet_bound n 1 P hP
  let r := min (R/2) (Δ/(2*L))
  have hr : 0 < r := lt_min (half_pos hR) (div_pos hΔ (by positivity))
  refine ⟨r,hr,min_le_left _ _,?_⟩
  intro Ω hΩ X hX z hRΩ hjets B hB y hy
  have hZ : ∀ I : ShortWord w s, ContDiffOn ℝ (⊤ : ℕ∞) (shortField w X I) Ω :=
    fun I => shortField_contDiffOn hΩ hX I
  have hZjet : ∀ I : ShortWord w s, HasJetBound Ω (closedBall z R) (shortField w X I) 1 P :=
    fun I => mappedShortField_jet_bound hΩ hRΩ w X hX id hM hjets I
  have hdjet := hdet (ShortWord w s) Ω (closedBall z R) hΩ hRΩ (shortField w X) hZ hZjet B
  have hgrad := hdjet.fderiv hΩ hRΩ
  have hdf : ∀ v ∈ closedBall z R, ‖fderiv ℝ (frameDet (shortField w X) B) v‖ ≤ L := by
    intro v hv
    simpa only [norm_iteratedFDerivWithin_zero] using hgrad 0 le_rfl v hv
  have hdiff : ∀ v ∈ closedBall z R, DifferentiableAt ℝ (frameDet (shortField w X) B) v :=
    fun v hv => ((frameDet_contDiffOn hZ B).contDiffAt (hΩ.mem_nhds (hRΩ hv))).differentiableAt (by simp)
  have hyR : y ∈ closedBall z R := closedBall_subset_closedBall
    ((min_le_left _ _).trans (half_le_self hR.le)) hy
  have hh := (convex_closedBall z R).norm_image_sub_le_of_norm_fderiv_le hdiff hdf
    (mem_closedBall_self hR.le) hyR
  have hyNorm : ‖y-z‖ ≤ r := by simpa only [mem_closedBall,dist_eq_norm] using hy
  have hsmall : L*r ≤ Δ/2 := by
    have hh' := (le_div_iff₀ (by positivity : 0 < 2*L)).mp (min_le_right (R/2) (Δ/(2*L)))
    dsimp [r]
    nlinarith
  have hvar : |frameDet (shortField w X) B y - frameDet (shortField w X) B z| ≤ Δ/2 := by
    rw [Real.norm_eq_abs] at hh
    exact hh.trans ((mul_le_mul_of_nonneg_left hyNorm hL.le).trans hsmall)
  have ha := abs_sub_abs_le_abs_sub (frameDet (shortField w X) B z) (frameDet (shortField w X) B y)
  rw [abs_sub_comm] at ha
  linarith
end RothschildStein.G4
