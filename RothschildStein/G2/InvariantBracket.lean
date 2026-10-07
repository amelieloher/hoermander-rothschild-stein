-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.G2.InvariantBasis
public import Mathlib.Algebra.Lie.Basic

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false

@[expose] public section
noncomputable section
namespace RothschildStein.G2
variable {N : ℕ} (G : HomogeneousGroup N)

/-- Translation covariance is closed under the vector-field Lie bracket
(BB Proposition 3.26, pp. 109–110). -/
theorem IsLeftInvariantField.lieBracket
    {V W : (Fin N → ℝ) → (Fin N → ℝ)}
    (hV : IsLeftInvariantField G V) (hW : IsLeftInvariantField G W) :
    IsLeftInvariantField G (VectorField.lieBracket ℝ V W) := by
  have hsV : ContDiff ℝ (⊤ : ℕ∞) V := by
    rw [hV.eq_leftField G]; exact contDiff_leftField G _
  have hsW : ContDiff ℝ (⊤ : ℕ∞) W := by
    rw [hW.eq_leftField G]; exact contDiff_leftField G _
  intro x y
  have heV : (fun z => fderiv ℝ (G.mul x) z (V z)) = V ∘ G.mul x :=
    funext (hV x)
  have heW : (fun z => fderiv ℝ (G.mul x) z (W z)) = W ∘ G.mul x :=
    funext (hW x)
  rw [VectorField.fderiv_apply_lieBracket (contDiff_leftTranslation G x).contDiffAt
    (by simp)
    (hsW.differentiable (by simp)).differentiableAt
    (hsV.differentiable (by simp)).differentiableAt, heV, heW]
  rw [fderiv_comp y (hsW.differentiable (by simp)).differentiableAt
    ((contDiff_leftTranslation G x).differentiable (by simp)).differentiableAt,
    fderiv_comp y (hsV.differentiable (by simp)).differentiableAt
    ((contDiff_leftTranslation G x).differentiable (by simp)).differentiableAt]
  simp only [ContinuousLinearMap.comp_apply, hV x y, hW x y, VectorField.lieBracket_eq]

end RothschildStein.G2
