-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.G4.LinearPaths
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set Metric
open scoped ENNReal
namespace RothschildStein.G4

/-- A smooth spanning family has a compact-buffer uniform
Euclidean-to-control bound of gain 1/s. This is used for the auxiliary
approximation residual, without ordinary-distance topology comparison
(BB Proposition 9.7 and proof of Theorem 9.58). -/
theorem exists_spanning_local_control_upper {m n s : ℕ}
    (hs : 0 < s) {Ω : Set (Fin n → ℝ)} (hΩ : IsOpen Ω)
    (w : Fin m → ℕ+) (Z : Fin m → (Fin n → ℝ) → (Fin n → ℝ))
    (hZ : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (Z i) Ω)
    (hw : ∀ i, (w i : ℕ) ≤ s) {z : Fin n → ℝ} (hz : z ∈ Ω)
    (hspan : ∃ B : Fin n → Fin m, frameDet Z B z ≠ 0) :
    ∃ R C : ℝ, 0 < R ∧ 0 < C ∧ closedBall z R ⊆ Ω ∧
      ∀ x ∈ closedBall z R, ∀ y ∈ closedBall z R, C * ‖y - x‖ ≤ 1 →
        controlDistance Ω w Z x y ≤ ENNReal.ofReal ((C * ‖y - x‖) ^ (1 / (s : ℝ))) := by
  obtain ⟨B, R, hR, C, hC, hRΩ, hB, hbound⟩ := exists_local_frame_bound hΩ hZ hz hspan
  refine ⟨R, C, hR, hC, hRΩ, ?_⟩
  intro x hx y hy hsmall
  by_cases he : y = x
  · subst y
    rw [G1.controlDistance_self (Ω := Ω) w Z (hRΩ hx)]
    exact bot_le
  have hn : 0 < ‖y - x‖ := norm_pos_iff.mpr (sub_ne_zero.mpr he)
  have hprod : 0 < C * ‖y - x‖ := mul_pos hC hn
  have ha : 0 < 1 / (s : ℝ) := by positivity
  let δ := (C * ‖y - x‖) ^ (1 / (s : ℝ))
  have hδ : 0 < δ := Real.rpow_pos_of_pos hprod _
  have hδone : δ ≤ 1 := by
    simpa only [Real.one_rpow] using Real.rpow_le_rpow hprod.le hsmall ha.le
  have hpower : δ ^ s = C * ‖y - x‖ := by
    dsimp [δ]
    rw [← Real.rpow_natCast, ← Real.rpow_mul hprod.le,
      one_div_mul_cancel (by positivity : (s : ℝ) ≠ 0), Real.rpow_one]
  exact controlDistance_lineMap_le hZ w hw B (convex_closedBall z R) hRΩ hB hbound
    hx hy hδ hδone hpower.ge

/-- The genuine short-bracket auxiliary distance has the
uniform residual bound on a derived compact original-domain buffer. -/
theorem exists_auxiliary_local_control_upper {m n s : ℕ}
    (hs : 0 < s) {Ω : Set (Fin n → ℝ)} (hΩ : IsOpen Ω)
    (w : Fin m → ℕ+) (X : Fin m → (Fin n → ℝ) → (Fin n → ℝ))
    (hX : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (X i) Ω)
    (hstep : bracketStepOn Ω w X s) {z : Fin n → ℝ} (hz : z ∈ Ω) :
    ∃ R C : ℝ, 0 < R ∧ 0 < C ∧ closedBall z R ⊆ Ω ∧
      ∀ x ∈ closedBall z R, ∀ y ∈ closedBall z R, C * ‖y - x‖ ≤ 1 →
        auxiliaryDistance (s := s) Ω w X x y ≤
          ENNReal.ofReal ((C * ‖y - x‖) ^ (1 / (s : ℝ))) := by
  apply exists_spanning_local_control_upper hs hΩ
    (fun j => shortWeight w (shortIndex (s := s) w j))
    (fun j => shortField w X (shortIndex (s := s) w j))
    (fun j => shortField_contDiffOn hΩ hX (shortIndex w j))
    (fun j => ((mem_shortWordFamily_iff w (shortIndex w j).val).mp
      (shortIndex w j).property).2) hz
  obtain ⟨B, hB⟩ := exists_short_frame hstep hz
  refine ⟨fun i => Fintype.equivFin (ShortWord w s) (B i), ?_⟩
  have hmat : frameMatrix (fun j => shortField w X (shortIndex w j))
      (fun i => Fintype.equivFin (ShortWord w s) (B i)) z =
      frameMatrix (shortField w X) B z := by
    ext a b
    simp only [frameMatrix, shortIndex, Equiv.symm_apply_apply]
  unfold frameDet
  rw [hmat]
  exact hB

end RothschildStein.G4
