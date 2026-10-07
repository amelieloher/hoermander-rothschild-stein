-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H3.AdjointTestRestriction
public import Mathlib.MeasureTheory.Measure.OpenPos

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
open Set MeasureTheory TopologicalSpace
namespace RothschildStein.H3

/-- Continuous real representatives of one distribution agree
pointwise on their open overlap, so Holder patches can be glued. -/
theorem real_distribution_representatives_agree {N : ℕ}
    (Ω U V : Opens (Fin N → ℝ)) (hU : U ≤ Ω) (hV : V ≤ Ω)
    (f g : (Fin N → ℝ) → ℝ) (hf : ContinuousOn f (U : Set (Fin N → ℝ)))
    (hg : ContinuousOn g (V : Set (Fin N → ℝ)))
    (T : Distribution Ω ℝ (⊤ : ℕ∞))
    (hTf : ∀ ψ : TestFunction U ℝ (⊤ : ℕ∞), T (TestFunction.monoCLM ℝ ψ) = ∫ x, ψ x * f x)
    (hTg : ∀ ψ : TestFunction V ℝ (⊤ : ℕ∞), T (TestFunction.monoCLM ℝ ψ) = ∫ x, ψ x * g x) :
    EqOn f g ((U : Set (Fin N → ℝ)) ∩ (V : Set (Fin N → ℝ))) := by
  let W := U ⊓ V
  have hfW : LocallyIntegrableOn f (W : Set (Fin N → ℝ)) volume := (hf.mono inter_subset_left).locallyIntegrableOn W.isOpen.measurableSet
  have hgW : LocallyIntegrableOn g (W : Set (Fin N → ℝ)) volume := (hg.mono inter_subset_right).locallyIntegrableOn W.isOpen.measurableSet
  have he : Distribution.ofFun W f volume (⊤ : ℕ∞) = Distribution.ofFun W g volume (⊤ : ℕ∞) := by
    ext ψ
    have hhf := hTf (TestFunction.monoCLM ℝ ψ)
    have hhg := hTg (TestFunction.monoCLM ℝ ψ)
    rw [test_mono_comp Ω U W hU inf_le_left] at hhf
    rw [test_mono_comp Ω V W hV inf_le_right] at hhg
    rw [Distribution.ofFun_apply hfW, Distribution.ofFun_apply hgW]
    simpa [TestFunction.monoCLM_apply, smul_eq_mul, W] using hhf.symm.trans hhg
  have hae := Distribution.ofFun_injective hfW hgW he
  exact MeasureTheory.Measure.eqOn_open_of_ae_eq hae W.isOpen
    (hf.mono inter_subset_left) (hg.mono inter_subset_right)

end RothschildStein.H3
