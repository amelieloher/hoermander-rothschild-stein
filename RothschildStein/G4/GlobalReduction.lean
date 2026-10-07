-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.G4.Frames

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set
open scoped BigOperators

namespace RothschildStein.G4

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {n : ℕ}

/-- The sum of squared frame determinants, defined without choosing
one frame or a partition of unity. -/
def determinantSquareSum (Z : ι → (Fin n → ℝ) → (Fin n → ℝ)) (x : Fin n → ℝ) : ℝ :=
  ∑ B : Fin n → ι, (frameDet Z B x) ^ 2

/-- Globally defined reduction coefficients from the adjugate
identities, with every occurrence of a short field collected. -/
def reductionCoefficient (Z : ι → (Fin n → ℝ) → (Fin n → ℝ))
    (V : (Fin n → ℝ) → (Fin n → ℝ)) (J : ι) (x : Fin n → ℝ) : ℝ :=
  (∑ B : Fin n → ι, ∑ i : Fin n,
    if B i = J then frameDet Z B x * replacementDet Z B (V x) i x else 0) /
      determinantSquareSum Z x

omit [DecidableEq ι] in
/-- Positivity follows from any nondegenerate frame
(BB Lemma 9.31, pp. 422–423). -/
theorem determinantSquareSum_pos {Z : ι → (Fin n → ℝ) → (Fin n → ℝ)}
    {x : Fin n → ℝ} (hframe : ∃ B : Fin n → ι, frameDet Z B x ≠ 0) :
    0 < determinantSquareSum Z x := by
  obtain ⟨B, hB⟩ := hframe
  exact (sq_pos_of_ne_zero hB).trans_le
    (Finset.single_le_sum (fun C _ => sq_nonneg (frameDet Z C x)) (Finset.mem_univ B))

omit [DecidableEq ι] in
/-- The squared-determinant denominator is smooth
(BB Lemma 9.31, pp. 422–423). -/
theorem determinantSquareSum_contDiffOn {Ω : Set (Fin n → ℝ)}
    {Z : ι → (Fin n → ℝ) → (Fin n → ℝ)}
    (hZ : ∀ J, ContDiffOn ℝ (⊤ : ℕ∞) (Z J) Ω) :
    ContDiffOn ℝ (⊤ : ℕ∞) (determinantSquareSum Z) Ω := by
  exact ContDiffOn.sum (fun B _ => (frameDet_contDiffOn hZ B).pow 2)

/-- Smooth global coefficients on any spanning open patch; even
singular individual frames cause no pole (BB Lemma 9.31, pp. 422–423). -/
theorem reductionCoefficient_contDiffOn {Ω : Set (Fin n → ℝ)}
    {Z : ι → (Fin n → ℝ) → (Fin n → ℝ)}
    (hZ : ∀ J, ContDiffOn ℝ (⊤ : ℕ∞) (Z J) Ω)
    {V : (Fin n → ℝ) → (Fin n → ℝ)} (hV : ContDiffOn ℝ (⊤ : ℕ∞) V Ω)
    (hspan : ∀ x ∈ Ω, ∃ B : Fin n → ι, frameDet Z B x ≠ 0) (J : ι) :
    ContDiffOn ℝ (⊤ : ℕ∞) (reductionCoefficient Z V J) Ω := by
  apply ContDiffOn.div _ (determinantSquareSum_contDiffOn hZ)
    (fun x hx => ne_of_gt (determinantSquareSum_pos (hspan x hx)))
  apply ContDiffOn.sum
  intro B hB
  apply ContDiffOn.sum
  intro i hi
  split_ifs
  · exact (frameDet_contDiffOn hZ B).mul (replacementDet_contDiffOn hZ hV B i)
  · exact contDiffOn_const

/-- The constructed global coefficients represent the actual field
at every point with at least one nondegenerate short frame (BB Lemma 9.31,
pp. 422–423). -/
theorem global_reduction_representation
    (Z : ι → (Fin n → ℝ) → (Fin n → ℝ))
    (V : (Fin n → ℝ) → (Fin n → ℝ)) {x : Fin n → ℝ}
    (hspan : ∃ B : Fin n → ι, frameDet Z B x ≠ 0) :
    V x = ∑ J, reductionCoefficient Z V J x • Z J x := by
  have hS : determinantSquareSum Z x ≠ 0 := ne_of_gt (determinantSquareSum_pos hspan)
  have hsum : determinantSquareSum Z x • V x =
      ∑ B : Fin n → ι, ∑ i : Fin n,
        (frameDet Z B x * replacementDet Z B (V x) i x) • Z (B i) x := by
    unfold determinantSquareSum
    rw [Finset.sum_smul]
    apply Finset.sum_congr rfl
    intro B hB
    calc
      (frameDet Z B x) ^ 2 • V x = frameDet Z B x • (frameDet Z B x • V x) := by
        rw [smul_smul, pow_two]
      _ = frameDet Z B x • (∑ i, replacementDet Z B (V x) i x • Z (B i) x) :=
        congrArg (fun v : Fin n → ℝ => frameDet Z B x • v)
          (frame_adjugate_identity Z B (V x) x)
      _ = _ := by rw [Finset.smul_sum]; simp only [smul_smul]
  have hcol : (∑ J, (∑ B : Fin n → ι, ∑ i : Fin n,
      if B i = J then frameDet Z B x * replacementDet Z B (V x) i x else 0) • Z J x) =
      ∑ B : Fin n → ι, ∑ i : Fin n,
        (frameDet Z B x * replacementDet Z B (V x) i x) • Z (B i) x := by
    simp only [Finset.sum_smul]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro B hB
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i hi
    simp [ite_smul]
  have h := congrArg (fun v : Fin n → ℝ => (determinantSquareSum Z x)⁻¹ • v) hsum
  rw [smul_smul, inv_mul_cancel₀ hS, one_smul, ← hcol, Finset.smul_sum] at h
  simpa only [reductionCoefficient, smul_smul, div_eq_mul_inv, mul_comm] using h

end RothschildStein.G4
