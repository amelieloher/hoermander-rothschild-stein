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

/-- The literal fixed global drift equation supplies the exact
local adjoint pairing on every open patch. No local regularity is used. -/
theorem local_adjoint_equation_of_global_frozen_drift_equation {n q : ℕ}
    (X : Fin (q + 1) → (Fin n → ℝ) → (Fin n → ℝ))
    (hX : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (X i))
    (u g : (Fin n → ℝ) → ℝ)
    (heq : hasDistributionEquationWithDrift ⊤ X (fun i => (hX i).contDiffOn)
      (Distribution.ofFun ⊤ u volume (⊤ : ℕ∞)) g)
    (U : Opens (Fin n → ℝ)) (ψ : TestFunction U ℝ (⊤ : ℕ∞)) :
    Distribution.ofFun ⊤ u volume (⊤ : ℕ∞)
      (TestFunction.monoCLM ℝ
        (Distribution.adjointTest U X (fun _ => 0)
          (fun i => (hX i).contDiffOn) (by fun_prop) ψ)) =
      Distribution.ofFun U g volume (⊤ : ℕ∞) ψ := by
  have hh := heq.2 (TestFunction.monoCLM ℝ ψ)
  change Distribution.ofFun ⊤ u volume (⊤ : ℕ∞)
    (driftTransposeTest ⊤ X (fun i => (hX i).contDiffOn) (TestFunction.monoCLM ℝ ψ)) = _ at hh
  rw [← adjointTest_zero_eq_driftTransposeTest,
    ← adjointTest_mono ⊤ U le_top X (fun _ => 0)
      (fun i => (hX i).contDiffOn) (by fun_prop)] at hh
  have hext : Distribution.ofFun ⊤ g volume (⊤ : ℕ∞) (TestFunction.monoCLM ℝ ψ) =
      Distribution.ofFun U g volume (⊤ : ℕ∞) ψ := by
    rw [Distribution.ofFun_apply heq.1, Distribution.ofFun_apply (heq.1.mono_set (subset_univ _))]
    simp [TestFunction.monoCLM_apply]
  exact hh.trans hext

end RothschildStein.H3
