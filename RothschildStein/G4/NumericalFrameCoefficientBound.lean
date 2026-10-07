-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module
public import RothschildStein.G4.FrameDetJetBounds
public import RothschildStein.G4.FrameBounds
@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set
namespace RothschildStein.G4

/-- Uniform numerical Cramer bounds from field values and a determinant floor. -/
theorem exists_numerical_frame_coefficient_bound (n : ℕ) (P Δ : ℝ)
    (hP : 0 ≤ P) (hΔ : 0 < Δ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (ι : Type*) (Ω K : Set (Fin n → ℝ)),
      IsOpen Ω → K ⊆ Ω →
      ∀ (Z : ι → (Fin n → ℝ) → (Fin n → ℝ)),
      (∀ j, ContDiffOn ℝ (⊤ : ℕ∞) (Z j) Ω) →
      (∀ j, HasJetBound Ω K (Z j) 0 P) →
      ∀ B : Fin n → ι, (∀ x ∈ K, Δ ≤ |frameDet Z B x|) →
      ∀ x ∈ K, ∀ i (v : Fin n → ℝ),
        |frameCoefficient Z B (fun _ => v) i x| ≤ C * ‖v‖ := by
  classical
  obtain ⟨A,hA,hdet⟩ := exists_frameDet_jet_bound n 0 (max P 1) (le_max_of_le_left hP)
  let C := n * (A / Δ) + 1
  have hratio : 0 ≤ A / Δ := (div_pos hA hΔ).le
  refine ⟨C,by dsimp [C]; positivity,?_⟩
  intro ι Ω K hΩ hK Z hZ hjet B hB x hx i v
  let Z' : Sum ι (Fin n) → (Fin n → ℝ) → (Fin n → ℝ) :=
    Sum.elim Z (fun j _ => Pi.single j 1)
  let B' : Fin n → Sum ι (Fin n) := fun j => Sum.inl (B j)
  have hZ' : ∀ j, ContDiffOn ℝ (⊤ : ℕ∞) (Z' j) Ω := by
    intro j
    cases j with
    | inl j => exact hZ j
    | inr j => exact contDiffOn_const
  have hj' : ∀ j, HasJetBound Ω K (Z' j) 0 (max P 1) := by
    intro j a ha y hy
    have ha0 : a = 0 := Nat.eq_zero_of_le_zero ha
    subst a
    cases j with
    | inl j => exact (hjet j 0 le_rfl y hy).trans (le_max_left _ _)
    | inr j =>
      simp only [norm_iteratedFDerivWithin_zero]
      change ‖(Pi.single j 1 : Fin n → ℝ)‖ ≤ max P 1
      simpa only [Pi.norm_single, norm_one] using le_max_right P 1
  have hc : ∀ j, |frameCoefficient Z B (fun _ => Pi.single j 1) i x| ≤ A / Δ := by
    intro j
    have hd := hdet (Sum ι (Fin n)) Ω K hΩ hK Z' hZ' hj'
      (Function.update B' i (Sum.inr j)) 0 le_rfl x hx
    rw [norm_iteratedFDerivWithin_zero, Real.norm_eq_abs] at hd
    have he : replacementDet Z B (Pi.single j 1) i x =
        frameDet Z' (Function.update B' i (Sum.inr j)) x := by
      change replacementDet Z' B' (Z' (Sum.inr j) x) i x = _
      exact replacementDet_eq_update Z' B' (Sum.inr j) i x
    unfold frameCoefficient
    rw [abs_div, he]
    exact (div_le_div_of_nonneg_right hd (abs_nonneg _)).trans
      (div_le_div_of_nonneg_left hA.le hΔ (hB x hx))
  have hb := frameCoefficient_le_of_coordinate_bounds Z B (fun _ => v) i x hc
  exact hb.trans (mul_le_mul_of_nonneg_right (by dsimp [C]; linarith) (norm_nonneg v))
end RothschildStein.G4
