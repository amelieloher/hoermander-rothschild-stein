-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.Distribution.AdjointTest
public import RothschildStein.S.DistributionRestriction

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public section
noncomputable section
open Set MeasureTheory TopologicalSpace
namespace RothschildStein.Distribution

/-- the complex-output scalar adapter of S's
restriction map, using the same continuous zero extension of tests. -/
def restrictComplexDistribution {N : ℕ} (Ω U : Opens (Fin N → ℝ))
    (T : Distribution Ω ℂ (⊤ : ℕ∞)) : Distribution U ℂ (⊤ : ℕ∞) :=
  (TestFunction.monoCLM ℝ : TestFunction U ℝ (⊤ : ℕ∞) →L[ℝ]
    TestFunction Ω ℝ (⊤ : ℕ∞)).precompCompactConvergenceCLM ℂ T

/-- restriction acts on the same real test function
when the open sets are related by an actual inclusion. -/
theorem restrictComplexDistribution_apply {N : ℕ} (Ω U : Opens (Fin N → ℝ))
    (hU : U ≤ Ω) (T : Distribution Ω ℂ (⊤ : ℕ∞)) (ψ : TestFunction U ℝ (⊤ : ℕ∞)) :
    restrictComplexDistribution Ω U T ψ =
      T ⟨ψ, ψ.contDiff, ψ.hasCompactSupport, ψ.tsupport_subset.trans hU⟩ := by
  change T (TestFunction.monoCLM ℝ ψ) = _
  congr 1
  ext x
  exact congrFun (by simp [TestFunction.monoCLM_apply, hU]) x

/-- local coefficient replacement preserves the
literal distribution equation, including drift and zeroth order. -/
theorem distributionEquation_of_coefficients_eqOn {k N : ℕ}
    (Ω : Opens (Fin N → ℝ)) (T G : Distribution Ω ℂ (⊤ : ℕ∞))
    (X Y : Fin (k + 1) → (Fin N → ℝ) → (Fin N → ℝ)) (c d : (Fin N → ℝ) → ℝ)
    (hX : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (X i) (Ω : Set (Fin N → ℝ)))
    (hY : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (Y i) (Ω : Set (Fin N → ℝ)))
    (hc : ContDiffOn ℝ (⊤ : ℕ∞) c (Ω : Set (Fin N → ℝ)))
    (hd : ContDiffOn ℝ (⊤ : ℕ∞) d (Ω : Set (Fin N → ℝ)))
    (hXY : ∀ i, EqOn (X i) (Y i) (Ω : Set (Fin N → ℝ)))
    (hcd : EqOn c d (Ω : Set (Fin N → ℝ)))
    (heq : ∀ ψ : TestFunction Ω ℝ (⊤ : ℕ∞), T (adjointTest Ω X c hX hc ψ) = G ψ) :
    ∀ ψ : TestFunction Ω ℝ (⊤ : ℕ∞), T (adjointTest Ω Y d hY hd ψ) = G ψ := by
  intro ψ
  have htest : adjointTest Ω Y d hY hd ψ = adjointTest Ω X c hX hc ψ := by
    ext x
    exact (Hormander.F.hormanderAdjointTest_eq_of_eqOn_open Ω.isOpen X Y c d ψ
      hXY hcd ψ.tsupport_subset x).symm
  rw [htest]
  exact heq ψ

/-- the actual distribution equation restricts to
an arbitrary open subset, with the same coefficient functions. -/
theorem restrictComplexDistribution_equation {k N : ℕ}
    (Ω U : Opens (Fin N → ℝ)) (hU : U ≤ Ω)
    (T G : Distribution Ω ℂ (⊤ : ℕ∞))
    (X : Fin (k + 1) → (Fin N → ℝ) → (Fin N → ℝ)) (c : (Fin N → ℝ) → ℝ)
    (hX : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (X i) (Ω : Set (Fin N → ℝ)))
    (hc : ContDiffOn ℝ (⊤ : ℕ∞) c (Ω : Set (Fin N → ℝ)))
    (heq : ∀ ψ : TestFunction Ω ℝ (⊤ : ℕ∞), T (adjointTest Ω X c hX hc ψ) = G ψ) :
    ∀ ψ : TestFunction U ℝ (⊤ : ℕ∞),
      restrictComplexDistribution Ω U T
        (adjointTest U X c (fun i => (hX i).mono hU) (hc.mono hU) ψ) =
      restrictComplexDistribution Ω U G ψ := by
  intro ψ
  let φ : TestFunction Ω ℝ (⊤ : ℕ∞) :=
    ⟨ψ, ψ.contDiff, ψ.hasCompactSupport, ψ.tsupport_subset.trans hU⟩
  let A := adjointTest U X c (fun i => (hX i).mono hU) (hc.mono hU) ψ
  have ha : (⟨A, A.contDiff, A.hasCompactSupport, A.tsupport_subset.trans hU⟩ :
      TestFunction Ω ℝ (⊤ : ℕ∞)) = adjointTest Ω X c hX hc φ := by
    ext x
    rfl
  rw [restrictComplexDistribution_apply Ω U hU T, restrictComplexDistribution_apply Ω U hU G]
  rw [ha]
  exact heq φ

end RothschildStein.Distribution
