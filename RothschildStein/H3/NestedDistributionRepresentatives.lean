-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H3.SobolevRepresentativeTransport
public import RothschildStein.H3.AdjointTestRestriction

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
namespace RothschildStein.H3
open Set MeasureTheory TopologicalSpace

/-- Nested locally integrable representatives of the same
original distribution agree almost everywhere on the smaller patch. -/
theorem ae_eq_of_nested_distribution_representatives {n : ℕ}
    (Ω V U : Opens (Fin n → ℝ)) (hV : V ≤ Ω) (hU : U ≤ V)
    (T : Distribution Ω ℝ (⊤ : ℕ∞)) (u v : (Fin n → ℝ) → ℝ)
    (hu : LocallyIntegrableOn u (U : Set (Fin n → ℝ)) volume)
    (hv : LocallyIntegrableOn v (V : Set (Fin n → ℝ)) volume)
    (hru : ∀ ψ : TestFunction U ℝ (⊤ : ℕ∞),
      T (TestFunction.monoCLM ℝ ψ) = ∫ x, ψ x * u x)
    (hrv : ∀ ψ : TestFunction V ℝ (⊤ : ℕ∞),
      T (TestFunction.monoCLM ℝ ψ) = ∫ x, ψ x * v x) :
    u =ᵐ[volume.restrict (U : Set (Fin n → ℝ))] v := by
  apply Distribution.ofFun_injective hu (hv.mono_set hU)
  ext ψ
  rw [Distribution.ofFun_apply hu, Distribution.ofFun_apply (hv.mono_set hU)]
  simp only [smul_eq_mul]
  have hh := hrv (TestFunction.monoCLM ℝ ψ)
  rw [test_mono_comp Ω V U hV hU, hru ψ] at hh
  simpa [TestFunction.monoCLM_apply, hU] using hh

end RothschildStein.H3
