-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.P1.PaddingDistributionDescent

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
open Set MeasureTheory TopologicalSpace
open scoped ENNReal
namespace RothschildStein.P1

/-- The padded tensor of a locally integrable forcing
function is exactly its pullback by the base projection, as an actual
distribution on the bounded cylinder. This identifies the right-hand
side of the padded equation with the function used in norm estimates. -/
theorem paddingDistributionTensorOneCLM_ofFun {n d : ℕ}
    (Ω : Opens (Fin n → ℝ)) (J : Opens (Fin d → ℝ))
    (hJ : volume (J : Set (Fin d → ℝ)) ≠ ⊤)
    (f : (Fin n → ℝ) → ℝ)
    (hf : LocallyIntegrableOn f (Ω : Set (Fin n → ℝ)) volume) :
    paddingDistributionTensorOneCLM Ω (P2.cylinder Ω J)
      (padding_cylinder_subset_base Ω J) (Distribution.ofFun Ω f volume (⊤ : ℕ∞)) =
      Distribution.ofFun (P2.cylinder Ω J) (fun ξ => f (basePoint ξ)) volume (⊤ : ℕ∞) := by
  let S : P2.FiberSetting (P2.cylinder Ω J) Ω := fiberSetting_padding_cylinder Ω J hJ
  ext ψ
  rw [paddingDistributionTensorOneCLM_apply,
    paddingFiberTestCLM_eq_fiberSetting_test Ω J S ψ]
  exact S.ofFun_test hf ψ

end RothschildStein.P1
