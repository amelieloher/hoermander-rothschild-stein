-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H1.OrderZeroFunctional

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
open TopologicalSpace
namespace RothschildStein.H1
variable {N : ℕ} (Ω : Opens (Fin N → ℝ))

/-- Restriction of an order-zero distribution to smooth tests
(BB p. 250; the bounded-continuous-function topology permits restriction to smooth tests). -/
def smoothOrderZeroDistribution
    (T : BoundedContinuousFunction (Fin N → ℝ) ℝ →L[ℝ] ℝ) :
    Distribution Ω ℝ (⊤ : ℕ∞) :=
  (orderZeroDistribution Ω T).comp (TestFunction.monoCLM ℝ)

/-- The restriction retains the bounded functional's action on
all smooth tests (BB p. 250). -/
theorem smoothOrderZeroDistribution_apply
    (T : BoundedContinuousFunction (Fin N → ℝ) ℝ →L[ℝ] ℝ)
    (φ : TestFunction Ω ℝ (⊤ : ℕ∞)) :
    smoothOrderZeroDistribution Ω T φ =
      T ((TestFunction.toBoundedContinuousFunctionCLM ℝ) φ) := by
  change T ((TestFunction.toBoundedContinuousFunctionCLM ℝ)
    ((TestFunction.monoCLM ℝ) φ : TestFunction Ω ℝ 0)) = _
  congr 1
  ext x
  simp


end RothschildStein.H1
