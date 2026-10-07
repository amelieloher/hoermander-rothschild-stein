-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.G2.WeightSpaces

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false

@[expose] public section
noncomputable section
namespace RothschildStein.G2
variable {N : ℕ} (G : HomogeneousGroup N)

/-- Brackets add homogeneity degrees (BB Proposition 3.35, p. 114). -/
theorem IsHomogeneousField.lieBracket
    {V W : (Fin N → ℝ) → (Fin N → ℝ)} {a b : ℝ}
    (hV : IsHomogeneousField G V a) (hW : IsHomogeneousField G W b)
    (hsV : ContDiff ℝ (⊤ : ℕ∞) V) (hsW : ContDiff ℝ (⊤ : ℕ∞) W) :
    IsHomogeneousField G (VectorField.lieBracket ℝ V W) (a + b) := by
  intro t ht x
  have heV : (fun z => fderiv ℝ (G.dilate t) z (V z)) =
      fun z => t ^ a • V (G.dilate t z) := by
    funext z
    rw [(hasFDerivAt_dilate G t z).fderiv, dilationDifferential_apply, hV t ht z]
  have heW : (fun z => fderiv ℝ (G.dilate t) z (W z)) =
      fun z => t ^ b • W (G.dilate t z) := by
    funext z
    rw [(hasFDerivAt_dilate G t z).fderiv, dilationDifferential_apply, hW t ht z]
  have hb := VectorField.fderiv_apply_lieBracket (contDiff_dilate G t).contDiffAt
    (by simp : minSmoothness ℝ 2 ≤ (⊤ : ℕ∞))
    (hsW.differentiable (by simp)).differentiableAt
    (hsV.differentiable (by simp)).differentiableAt
    (x := x)
  rw [(hasFDerivAt_dilate G t x).fderiv, dilationDifferential_apply, heV, heW] at hb
  have hcV : DifferentiableAt ℝ (V ∘ G.dilate t) x :=
    (hsV.differentiable (by simp)).differentiableAt.comp x
      (hasFDerivAt_dilate G t x).differentiableAt
  have hcW : DifferentiableAt ℝ (W ∘ G.dilate t) x :=
    (hsW.differentiable (by simp)).differentiableAt.comp x
      (hasFDerivAt_dilate G t x).differentiableAt
  have hdW : fderiv ℝ (fun z => t ^ b • W (G.dilate t z)) x =
      t ^ b • fderiv ℝ (W ∘ G.dilate t) x := by
    convert fderiv_fun_const_smul (𝕜 := ℝ) (R := ℝ) hcW (t ^ b) using 1
    congr 1
  have hdV : fderiv ℝ (fun z => t ^ a • V (G.dilate t z)) x =
      t ^ a • fderiv ℝ (V ∘ G.dilate t) x := by
    convert fderiv_fun_const_smul (𝕜 := ℝ) (R := ℝ) hcV (t ^ a) using 1
    congr 1
  rw [hdW, hdV,
    fderiv_comp x (hsW.differentiable (by simp)).differentiableAt
      (hasFDerivAt_dilate G t x).differentiableAt,
    fderiv_comp x (hsV.differentiable (by simp)).differentiableAt
      (hasFDerivAt_dilate G t x).differentiableAt,
    (hasFDerivAt_dilate G t x).fderiv] at hb
  simp only [smul_apply, ContinuousLinearMap.comp_apply,
    dilationDifferential_apply, hV t ht x, hW t ht x, map_smul, smul_smul] at hb
  rw [hb, Real.rpow_add ht, VectorField.lieBracket_eq, smul_sub]
  congr 1
  rw [mul_comm]

end RothschildStein.G2
