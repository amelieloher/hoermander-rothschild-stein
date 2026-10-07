-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H3.AdjointTestRestriction
public import RothschildStein.Definitions.hasDistributionEquationWithDrift

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public section
noncomputable section
namespace RothschildStein.H3
open Set MeasureTheory TopologicalSpace

/-- The literal fixed equation for an arbitrary distribution
supplies its exact adjoint equation on every interior open patch. -/
theorem patch_adjoint_equation_of_frozen_drift_equation {n q : ℕ}
    (Ω V : Opens (Fin n → ℝ)) (hV : V ≤ Ω)
    (X : Fin (q + 1) → (Fin n → ℝ) → (Fin n → ℝ))
    (hX : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (X i) (Ω : Set (Fin n → ℝ)))
    (T : Distribution Ω ℝ (⊤ : ℕ∞)) (g : (Fin n → ℝ) → ℝ)
    (heq : hasDistributionEquationWithDrift Ω X hX T g)
    (ψ : TestFunction V ℝ (⊤ : ℕ∞)) :
    T (TestFunction.monoCLM ℝ
      (Distribution.adjointTest V X (fun _ => 0)
        (fun i => (hX i).mono hV) (by fun_prop) ψ)) =
      Distribution.ofFun V g volume (⊤ : ℕ∞) ψ := by
  have hh := heq.2 (TestFunction.monoCLM ℝ ψ)
  change T (driftTransposeTest Ω X hX (TestFunction.monoCLM ℝ ψ)) = _ at hh
  rw [← adjointTest_zero_eq_driftTransposeTest,
    ← adjointTest_mono Ω V hV X (fun _ => 0) hX (by fun_prop)] at hh
  have hext : Distribution.ofFun Ω g volume (⊤ : ℕ∞) (TestFunction.monoCLM ℝ ψ) =
      Distribution.ofFun V g volume (⊤ : ℕ∞) ψ := by
    rw [Distribution.ofFun_apply heq.1, Distribution.ofFun_apply (heq.1.mono_set hV)]
    simp [TestFunction.monoCLM_apply, hV]
  exact hh.trans hext

end RothschildStein.H3
