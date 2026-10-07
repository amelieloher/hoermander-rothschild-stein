-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.P1.PaddingCylinderFiberSetting
public import RothschildStein.P1.PaddingDistributionTensorDefs
public import RothschildStein.P2.SmoothingDescent

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
open Set MeasureTheory TopologicalSpace
namespace RothschildStein.P1

/-- A locally integrable representative of the actual padded
tensor distribution descends by a compact normalized fiber test.
The lifted representative equals the descended function almost everywhere;
no function-valued premise is imposed on the original distribution. -/
theorem paddingDistributionTensor_descent {n d : ℕ}
    (Ω : Opens (Fin n → ℝ)) (J : Opens (Fin d → ℝ))
    (hJ : volume (J : Set (Fin d → ℝ)) ≠ ⊤)
    (η : _root_.TestFunction J ℝ ⊤) (hη : ∫ z, η z = 1)
    (T : Distribution Ω ℝ (⊤ : ℕ∞))
    (v : (Fin (n + d) → ℝ) → ℝ)
    (hv : LocallyIntegrableOn v (P2.cylinder Ω J : Set (Fin (n + d) → ℝ)) volume)
    (hT : paddingDistributionTensorOneCLM Ω (P2.cylinder Ω J) (padding_cylinder_subset_base Ω J) T =
      Distribution.ofFun (P2.cylinder Ω J) v volume (⊤ : ℕ∞)) :
    representsDistribution Ω T (P2.fiberAvg v η) ∧
      v =ᵐ[volume.restrict (P2.cylinder Ω J : Set (Fin (n + d) → ℝ))]
        fun ξ => P2.fiberAvg v η (basePoint ξ) := by
  let S : P2.FiberSetting (P2.cylinder Ω J) Ω := fiberSetting_padding_cylinder Ω J hJ
  apply P2.descent_of_lift S hη T hv
  intro ψ
  rw [← paddingFiberTestCLM_eq_fiberSetting_test Ω J S ψ,
    ← paddingDistributionTensorOneCLM_apply]
  exact congrArg (fun D : Distribution (P2.cylinder Ω J) ℝ (⊤ : ℕ∞) => D ψ) hT

end RothschildStein.P1
