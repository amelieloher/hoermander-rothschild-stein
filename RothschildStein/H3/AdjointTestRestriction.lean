-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H3.DriftAdjointBridge

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
namespace RothschildStein.H3
open Set TopologicalSpace

/-- actual adjoint tests commute with continuous extension
from the smaller open domain. The fields and coefficients are the same
functions on both domains. -/
theorem adjointTest_mono {n q : ℕ} (V U : Opens (Fin n → ℝ)) (hU : U ≤ V)
    (X : Fin (q+1) → (Fin n → ℝ) → (Fin n → ℝ)) (c : (Fin n → ℝ) → ℝ)
    (hXV : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (X i) (V : Set (Fin n → ℝ)))
    (hcV : ContDiffOn ℝ (⊤ : ℕ∞) c (V : Set (Fin n → ℝ)))
    (ψ : TestFunction U ℝ (⊤ : ℕ∞)) :
    (TestFunction.monoCLM ℝ
      (Distribution.adjointTest U X c (fun i => (hXV i).mono hU) (hcV.mono hU) ψ) :
      TestFunction V ℝ (⊤ : ℕ∞)) =
    Distribution.adjointTest V X c hXV hcV (TestFunction.monoCLM ℝ ψ) := by
  ext x
  have he : ((TestFunction.monoCLM ℝ ψ : TestFunction V ℝ (⊤ : ℕ∞)) :
      (Fin n → ℝ) → ℝ) = ψ := by simp [TestFunction.monoCLM_apply,hU]
  have ht : ((TestFunction.monoCLM ℝ
      (Distribution.adjointTest U X c (fun i => (hXV i).mono hU) (hcV.mono hU) ψ) :
      TestFunction V ℝ (⊤ : ℕ∞)) : (Fin n → ℝ) → ℝ) =
      Distribution.adjointTest U X c (fun i => (hXV i).mono hU) (hcV.mono hU) ψ := by
    simp [TestFunction.monoCLM_apply,hU]
  change _ = Hormander.Interface.hormanderAdjointTest X c
    (TestFunction.monoCLM ℝ ψ : TestFunction V ℝ (⊤ : ℕ∞)) x
  rw [he]
  exact congrFun ht x

/-- Nested continuous extensions give the same test on the outer domain. -/
theorem test_mono_comp {n : ℕ} (Ω V U : Opens (Fin n → ℝ))
    (hV : V ≤ Ω) (hU : U ≤ V) (ψ : TestFunction U ℝ (⊤ : ℕ∞)) :
    (TestFunction.monoCLM ℝ
      (TestFunction.monoCLM ℝ ψ : TestFunction V ℝ (⊤ : ℕ∞)) :
      TestFunction Ω ℝ (⊤ : ℕ∞)) = TestFunction.monoCLM ℝ ψ := by
  ext x
  simp [TestFunction.monoCLM_apply,hU,hV,hU.trans hV]

end RothschildStein.H3
