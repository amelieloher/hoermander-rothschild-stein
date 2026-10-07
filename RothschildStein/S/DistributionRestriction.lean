-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.S.TestOperators
public import Mathlib.Analysis.Calculus.ContDiff.Bounds
public import RothschildStein.S.DistributionWords

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
open Set MeasureTheory TopologicalSpace Filter
open scoped BigOperators Topology Distributions CompactConvergenceCLM
namespace RothschildStein.S
variable {n : ℕ}

/-- Transposition of a continuous test map is continuous in the
compact-convergence distribution topology (BB p. 68). -/
def testMapTransposeCLM (Ω U : Opens (Fin n → ℝ))
    (A : TestFunction Ω ℝ (⊤ : ℕ∞) →L[ℝ] TestFunction U ℝ (⊤ : ℕ∞)) :
    Distribution U ℝ (⊤ : ℕ∞) →L[ℝ] Distribution Ω ℝ (⊤ : ℕ∞) :=
  A.precompCompactConvergenceCLM ℝ

/-- Restriction to an open subset is the transpose of continuous
zero extension of tests (BB p. 68). -/
def distributionRestrictionCLM (Ω U : Opens (Fin n → ℝ)) :
    Distribution Ω ℝ (⊤ : ℕ∞) →L[ℝ] Distribution U ℝ (⊤ : ℕ∞) :=
  testMapTransposeCLM U Ω (TestFunction.monoCLM ℝ)

/-- For an open inclusion, restriction evaluates the same scalar
function viewed as a test on the larger open set (BB p. 68). -/
theorem distributionRestrictionCLM_apply (Ω U : Opens (Fin n → ℝ)) (hU : U ≤ Ω)
    (T : Distribution Ω ℝ (⊤ : ℕ∞)) (φ : TestFunction U ℝ (⊤ : ℕ∞)) :
    distributionRestrictionCLM Ω U T φ =
      T ⟨φ,φ.contDiff,φ.hasCompactSupport,φ.tsupport_subset.trans hU⟩ := by
  change T (TestFunction.monoCLM ℝ φ) = _
  congr 1
  ext x
  exact congrFun (by simp [TestFunction.monoCLM_apply,hU]) x

end RothschildStein.S
