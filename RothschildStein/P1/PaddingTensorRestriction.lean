-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.P1.PaddingDistributionTensorDefs
public import RothschildStein.S.DistributionRestriction

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public section
noncomputable section
open Set MeasureTheory TopologicalSpace
namespace RothschildStein.P1

/-- The actual tensor with one commutes with restriction to
any smaller open set projecting into a smaller base domain. This
allows norm and regularity descent on interior cylinders. -/
theorem paddingDistributionTensorOneCLM_restriction {n d : ℕ}
    (Ω V : Opens (Fin n → ℝ)) (hV : V ≤ Ω)
    (U W : Opens (Fin (n + d) → ℝ)) (hW : W ≤ U)
    (hU : (U : Set (Fin (n + d) → ℝ)) ⊆ basePoint ⁻¹' (Ω : Set (Fin n → ℝ)))
    (hWV : (W : Set (Fin (n + d) → ℝ)) ⊆ basePoint ⁻¹' (V : Set (Fin n → ℝ)))
    (T : Distribution Ω ℝ (⊤ : ℕ∞)) :
    S.distributionRestrictionCLM U W (paddingDistributionTensorOneCLM Ω U hU T) =
      paddingDistributionTensorOneCLM V W hWV (S.distributionRestrictionCLM Ω V T) := by
  ext φ
  rw [S.distributionRestrictionCLM_apply U W hW,
    paddingDistributionTensorOneCLM_apply, paddingDistributionTensorOneCLM_apply,
    S.distributionRestrictionCLM_apply Ω V hV]
  congr 1

end RothschildStein.P1
