-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.S.SobolevAE
public import Mathlib.Analysis.Distribution.Distribution

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public section
noncomputable section
namespace RothschildStein.H3
open Set MeasureTheory TopologicalSpace
open scoped ENNReal

/-- Equality of the original function distribution and an interior
representative identifies the functions almost everywhere on the patch. -/
theorem ae_eq_of_ofFun_patch_representation {n : ℕ}
    (Ω U : Opens (Fin n → ℝ)) (hU : U ≤ Ω) (u w : (Fin n → ℝ) → ℝ)
    (hu : LocallyIntegrableOn u (Ω : Set (Fin n → ℝ)) volume)
    (hw : LocallyIntegrableOn w (U : Set (Fin n → ℝ)) volume)
    (hrep : ∀ ψ : TestFunction U ℝ (⊤ : ℕ∞),
      Distribution.ofFun Ω u volume (⊤ : ℕ∞) (TestFunction.monoCLM ℝ ψ) =
        ∫ x, ψ x*w x) : u =ᵐ[volume.restrict (U : Set (Fin n → ℝ))] w := by
  apply Distribution.ofFun_injective (hu.mono_set hU) hw
  ext ψ
  have hh := hrep ψ
  rw [Distribution.ofFun_apply hu] at hh
  rw [Distribution.ofFun_apply (hu.mono_set hU), Distribution.ofFun_apply hw]
  simpa [TestFunction.monoCLM_apply, hU, smul_eq_mul] using hh

end RothschildStein.H3
