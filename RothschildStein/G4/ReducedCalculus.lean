-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.G4.BracketReduction
public import RothschildStein.G4.FrameCalculus
public import RothschildStein.G4.DeterminantDerivative

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set
open scoped BigOperators

namespace RothschildStein.G4

/-- Substitute the actual short-field bracket reduction into the
coefficient derivative, retaining both Leibniz contributions
(BB Proposition 9.36, pp. 427–428). -/
theorem fieldDerivative_frameCoefficient_of_bracket_reduction
    {ι : Type*} [Fintype ι] {n : ℕ} {Ω : Set (Fin n → ℝ)} (hΩ : IsOpen Ω)
    {Z : ι → (Fin n → ℝ) → (Fin n → ℝ)}
    (hZ : ∀ j, ContDiffOn ℝ (⊤ : ℕ∞) (Z j) Ω)
    (T : (Fin n → ℝ) → (Fin n → ℝ))
    (c : ι → ι → (Fin n → ℝ) → ℝ) (B : Fin n → ι)
    {x : Fin n → ℝ} (hx : x ∈ Ω) (hB : frameDet Z B x ≠ 0)
    (hc : ∀ J, VectorField.lieBracket ℝ T (Z J) x = ∑ K, c J K x • Z K x)
    (J : ι) (i : Fin n) :
    fieldDerivative T (frameCoefficient Z B (Z J) i) x =
      (∑ K, c J K x * frameCoefficient Z B (Z K) i x) -
        ∑ j, ∑ K, c (B j) K x *
          (frameCoefficient Z B (Z J) j x * frameCoefficient Z B (Z K) i x) := by
  rw [fieldDerivative_frameCoefficient hΩ hZ (hZ J) T B hx hB i]
  rw [frameCoefficient_linear_combination Z B _ _ i x (hc J)]
  congr 1
  apply Finset.sum_congr rfl
  intro j hj
  rw [frameCoefficient_linear_combination Z B _ _ i x (hc (B j)), Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro K hK
  ring

/-- Dividing a replacement determinant by a nonzero frame
and multiplying back recovers the numerator (BB (9.29), p. 429). -/
theorem replacementDet_eq_frameCoefficient_mul
    {ι : Type*} {n : ℕ} (Z : ι → (Fin n → ℝ) → (Fin n → ℝ))
    (B : Fin n → ι) (V : (Fin n → ℝ) → (Fin n → ℝ))
    (i : Fin n) {x : Fin n → ℝ} (hB : frameDet Z B x ≠ 0) :
    replacementDet Z B (V x) i x = frameCoefficient Z B V i x * frameDet Z B x := by
  simp only [frameCoefficient, div_mul_cancel₀ _ hB]

/-- The first determinant derivative factors as the frame
determinant times a sum of one-factor generators plus divergence
(BB Lemma 9.37, pp. 428–430). -/
theorem fieldDerivative_frameDet_of_bracket_reduction
    {ι : Type*} [Fintype ι] {n : ℕ}
    {Z : ι → (Fin n → ℝ) → (Fin n → ℝ)} (B : Fin n → ι)
    (T : (Fin n → ℝ) → (Fin n → ℝ)) (c : ι → ι → (Fin n → ℝ) → ℝ)
    {x : Fin n → ℝ} (hB : frameDet Z B x ≠ 0)
    (hZ : ∀ j, DifferentiableAt ℝ (Z (B j)) x)
    (hc : ∀ J, VectorField.lieBracket ℝ T (Z J) x = ∑ K, c J K x • Z K x) :
    fieldDerivative T (frameDet Z B) x =
      (Hormander.Interface.euclideanDivergence T x +
        ∑ j, ∑ K, c (B j) K x * frameCoefficient Z B (Z K) j x) * frameDet Z B x := by
  rw [fieldDerivative_frameDet_bracket B T hZ]
  simp_rw [replacementDet_eq_frameCoefficient_mul Z B _ _ hB]
  rw [← Finset.sum_mul, ← add_mul]
  congr 1
  congr 1
  apply Finset.sum_congr rfl
  intro j hj
  exact frameCoefficient_linear_combination Z B _ _ j x (hc (B j))

end RothschildStein.G4
