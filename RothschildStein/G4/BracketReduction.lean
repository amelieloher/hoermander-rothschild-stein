-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.G4.WeightedReduction
public import RothschildStein.G4.FrameBounds

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set Hormander.C
open scoped BigOperators

namespace RothschildStein.G4

/-- Reduce the entire binary bracket into short words using the
constant Jacobi expansion before introducing frame coefficients. -/
def binaryReductionCoefficient {k n s : ℕ} (w : Fin (k + 1) → ℕ+)
    (X : Fin (k + 1) → (Fin n → ℝ) → (Fin n → ℝ))
    (t : Hormander.Interface.LieWord k) : ShortWord w s → (Fin n → ℝ) → ℝ :=
  combinationReductionCoefficient w X (binaryExpansion t)

/-- The entire-bracket reduction is smooth on the original domain
(BB Lemmas 9.30–9.31, pp. 422–423). -/
theorem binaryReductionCoefficient_contDiffOn {k n s : ℕ}
    {Ω : Set (Fin n → ℝ)} (hΩ : IsOpen Ω) {w : Fin (k + 1) → ℕ+}
    {X : Fin (k + 1) → (Fin n → ℝ) → (Fin n → ℝ)}
    (hX : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (X i) Ω)
    (hstep : bracketStepOn Ω w X s) (t : Hormander.Interface.LieWord k) (J : ShortWord w s) :
    ContDiffOn ℝ (⊤ : ℕ∞) (binaryReductionCoefficient w X t J) Ω :=
  combinationReductionCoefficient_contDiffOn hΩ hX hstep _ J

/-- Vector identity for the entire-bracket reduction
(BB Lemmas 9.30–9.31, pp. 422–423). -/
theorem binary_reduction_representation {k n s : ℕ}
    {Ω : Set (Fin n → ℝ)} (hΩ : IsOpen Ω) {w : Fin (k + 1) → ℕ+}
    {X : Fin (k + 1) → (Fin n → ℝ) → (Fin n → ℝ)}
    (hX : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (X i) Ω)
    (hstep : bracketStepOn Ω w X s) (t : Hormander.Interface.LieWord k)
    {x : Fin n → ℝ} (hx : x ∈ Ω) :
    Hormander.lieWordEval X t x =
      ∑ J : ShortWord w s, binaryReductionCoefficient w X t J x • shortField w X J x := by
  rw [← binaryExpansion_eqOn hΩ X hX t hx]
  exact combination_reduction_representation hstep _ hx

/-- The reduction cannot increase the total bracket weight, including
drift weight two (BB Lemma 9.30, p. 422). -/
theorem binaryReductionCoefficient_eq_zero_of_weight_lt {k n s : ℕ}
    (w : Fin (k + 1) → ℕ+) (X : Fin (k + 1) → (Fin n → ℝ) → (Fin n → ℝ))
    (t : Hormander.Interface.LieWord k) (J : ShortWord w s)
    (hweight : G1.binaryWeight w t < wordWeight w J.val) :
    binaryReductionCoefficient w X t J = 0 :=
  combinationReductionCoefficient_eq_zero_of_weight_lt w X _ (G1.binaryExpansion_weight w t) J hweight

/-- Cramer's linearity transports an actual short-field
reduction to coefficients in any nondegenerate frame (BB (9.21), p. 424). -/
theorem frameCoefficient_linear_combination {ι : Type*} [Fintype ι] {n : ℕ}
    (Z : ι → (Fin n → ℝ) → (Fin n → ℝ)) (B : Fin n → ι)
    (V : (Fin n → ℝ) → (Fin n → ℝ)) (c : ι → ℝ) (i : Fin n) (x : Fin n → ℝ)
    (heq : V x = ∑ J, c J • Z J x) :
    frameCoefficient Z B V i x = ∑ J, c J * frameCoefficient Z B (Z J) i x := by
  unfold frameCoefficient
  change (Matrix.cramer (frameMatrix Z B x) (V x)) i / frameDet Z B x = _
  rw [heq, map_sum]
  simp only [map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Matrix.cramer_apply]
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro J hJ
  unfold replacementDet
  ring

/-- Combining the entire-bracket reduction with Cramer coefficients gives
the full formula, including variable-coefficient derivatives
(BB Proposition 9.32, pp. 424–425). -/
theorem binary_frameCoefficient_representation {k n s : ℕ}
    {Ω : Set (Fin n → ℝ)} (hΩ : IsOpen Ω) {w : Fin (k + 1) → ℕ+}
    {X : Fin (k + 1) → (Fin n → ℝ) → (Fin n → ℝ)}
    (hX : ∀ j, ContDiffOn ℝ (⊤ : ℕ∞) (X j) Ω)
    (hstep : bracketStepOn Ω w X s) (t : Hormander.Interface.LieWord k)
    (B : Fin n → ShortWord w s) (i : Fin n) {x : Fin n → ℝ} (hx : x ∈ Ω) :
    frameCoefficient (shortField w X) B (Hormander.lieWordEval X t) i x =
      ∑ J : ShortWord w s, binaryReductionCoefficient w X t J x *
        frameCoefficient (shortField w X) B (shortField w X J) i x :=
  frameCoefficient_linear_combination _ _ _ _ i x (binary_reduction_representation hΩ hX hstep t hx)

end RothschildStein.G4
