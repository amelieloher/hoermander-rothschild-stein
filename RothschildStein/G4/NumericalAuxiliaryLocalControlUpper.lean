-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module
public import RothschildStein.G4.NumericalLocalFrameBound
public import RothschildStein.G4.SpanningLocalControlUpper
@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set Metric
open scoped ENNReal
namespace RothschildStein.G4

/-- The auxiliary residual bound has constants fixed by primitive jet and
central rank budgets, before the actual fields are chosen. -/
theorem exists_numerical_auxiliary_local_control_upper {k n s : ℕ}
    (hs : 0 < s) (w : Fin (k+1) → ℕ+)
    (M Δ R : ℝ) (hM : 0 ≤ M) (hΔ : 0 < Δ) (hR : 0 < R) :
    ∃ r C : ℝ, 0 < r ∧ r ≤ R/2 ∧ 0 < C ∧
      ∀ (Ω : Set (Fin n → ℝ)), IsOpen Ω →
      ∀ (X : Fin (k+1) → (Fin n → ℝ) → (Fin n → ℝ)),
      (∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (X i) Ω) →
      ∀ z : Fin n → ℝ, closedBall z R ⊆ Ω →
      (∀ i, HasJetBound Ω (closedBall z R) (X i) (1+s) M) →
      (∃ B : Fin n → ShortWord w s, Δ ≤ |frameDet (shortField w X) B z|) →
      closedBall z r ⊆ Ω ∧
      ∀ x ∈ closedBall z r, ∀ y ∈ closedBall z r, C * ‖y-x‖ ≤ 1 →
        auxiliaryDistance (s := s) Ω w X x y ≤
          ENNReal.ofReal ((C * ‖y-x‖) ^ (1/(s : ℝ))) := by
  classical
  obtain ⟨r,C,hr,hrR,hC,hframe⟩ := exists_numerical_local_frame_bound w M Δ R hM hΔ hR
  refine ⟨r,C,hr,hrR,hC,?_⟩
  intro Ω hΩ X hX z hRΩ hjets hmax
  obtain ⟨B,hB⟩ := hmax
  obtain ⟨hrΩ,hBn,hcoef⟩ := hframe Ω hΩ X hX z hRΩ hjets B hB
  refine ⟨hrΩ,?_⟩
  intro x hx y hy hsmall
  by_cases he : y = x
  · subst y
    rw [show auxiliaryDistance (s := s) Ω w X x x = 0 from
      G1.controlDistance_self _ _ (hrΩ hx)]
    exact bot_le
  have hn : 0 < ‖y-x‖ := norm_pos_iff.mpr (sub_ne_zero.mpr he)
  have hprod : 0 < C * ‖y-x‖ := mul_pos hC hn
  let δ := (C * ‖y-x‖) ^ (1/(s : ℝ))
  have hδ : 0 < δ := Real.rpow_pos_of_pos hprod _
  have hδone : δ ≤ 1 := by
    simpa only [Real.one_rpow] using Real.rpow_le_rpow hprod.le hsmall (by positivity : 0 ≤ 1/(s : ℝ))
  have hpower : δ ^ s = C * ‖y-x‖ := by
    dsimp [δ]
    rw [← Real.rpow_natCast, ← Real.rpow_mul hprod.le,
      one_div_mul_cancel (by positivity : (s : ℝ) ≠ 0), Real.rpow_one]
  let Z := fun j => shortField w X (shortIndex (s := s) w j)
  let wf := fun j => shortWeight w (shortIndex (s := s) w j)
  let Bf := fun i => Fintype.equivFin (ShortWord w s) (B i)
  have hval : ∀ i, Z (Bf i) = shortField w X (B i) := by
    intro i
    simp [Z,Bf,shortIndex]
  have hdet : ∀ v, frameDet Z Bf v = frameDet (shortField w X) B v := by
    intro v
    unfold frameDet
    congr 1
    ext a b
    simp only [frameMatrix,hval]
  have hmat : ∀ v, frameMatrix Z Bf v = frameMatrix (shortField w X) B v := by
    intro v
    ext a b
    simp only [frameMatrix,hval]
  have hcf : ∀ v i u, frameCoefficient Z Bf (fun _ => u) i v =
      frameCoefficient (shortField w X) B (fun _ => u) i v := by
    intro v i u
    simp only [frameCoefficient,replacementDet,hdet,hmat]
  exact controlDistance_lineMap_le
    (fun j => shortField_contDiffOn hΩ hX (shortIndex w j)) wf
    (fun j => ((mem_shortWordFamily_iff w (shortIndex w j).val).mp (shortIndex w j).property).2)
    Bf (convex_closedBall z r) hrΩ (fun v hv => by rw [hdet]; exact hBn v hv)
    (fun v hv i u => by rw [hcf]; exact hcoef v hv i u) hx hy hδ hδone hpower.ge
end RothschildStein.G4
