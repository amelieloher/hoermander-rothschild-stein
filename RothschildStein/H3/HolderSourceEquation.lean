-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H3.IntrinsicSuffixWeakBridge
public import RothschildStein.H3.WeakOperatorDistributionEquation
public import RothschildStein.S.Sobolev
public import RothschildStein.Definitions.hasDistributionEquationWithDrift

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public section
noncomputable section
open Set MeasureTheory TopologicalSpace
open scoped BigOperators ENNReal
namespace RothschildStein.H3

/-- Actual continuous compact intrinsic jets yield the literal
fixed drift distribution equation for their drift-plus-square source. -/
theorem source_distribution_equation_of_intrinsic_jets {N q : ℕ}
    (X : Fin (q + 1) → (Fin N → ℝ) → (Fin N → ℝ))
    (hX : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (X i))
    (u : (Fin N → ℝ) → ℝ)
    (jet : List (Fin (q + 1)) → (Fin N → ℝ) → ℝ) (hzero : jet [] = u)
    (hi : ∀ I, wordWeight driftWeight I ≤ 2 → hasIntrinsicWordDeriv X ⊤ I u (jet I))
    (hc : ∀ I, wordWeight driftWeight I ≤ 2 → Continuous (jet I))
    (hs : ∀ I, wordWeight driftWeight I ≤ 2 → HasCompactSupport (jet I)) :
    hasDistributionEquationWithDrift ⊤ X (fun i => (hX i).contDiffOn)
      (Distribution.ofFun ⊤ u volume (⊤ : ℕ∞))
      (fun x => jet [0] x + ∑ i : Fin q, jet [i.succ, i.succ] x) := by
  classical
  have hw1 (i : Fin (q + 1)) : wordWeight driftWeight [i] ≤ 2 := by
    by_cases he : i = 0 <;> simp [wordWeight, driftWeight, he]
  have hw2 (i : Fin q) : wordWeight (driftWeight (q := q)) [i.succ, i.succ] ≤ 2 := by
    simp [wordWeight, driftWeight]
  have hw (I : List (Fin (q + 1))) (hI : wordWeight driftWeight I ≤ 2) :
      hasWeakWordDeriv X ⊤ I u (jet I) := by
    apply hasWeakWordDeriv_of_intrinsic_suffix_jets ⊤ X
      (fun i => (hX i).contDiffOn) I u jet hzero
    · intro J hJ
      exact hi J ((S.wordWeight_sublist_le driftWeight hJ.sublist).trans hI)
    · intro J hJ
      exact (hc J ((S.wordWeight_sublist_le driftWeight hJ.sublist).trans hI)).continuousOn
  let D : WeakDriftOperatorData X ⊤ 1 u := {
    first := fun i => jet [i]
    square := fun i => jet [i.succ, i.succ]
    first_weak := fun i => hw _ (hw1 i)
    square_weak := fun i => hw _ (hw2 i)
    first_memLp := fun i => by
      simpa only [Opens.coe_top, Measure.restrict_univ] using
        (hc _ (hw1 i)).memLp_of_hasCompactSupport (hs _ (hw1 i)) (p := 1)
    square_memLp := fun i => by
      simpa only [Opens.coe_top, Measure.restrict_univ] using
        (hc _ (hw2 i)).memLp_of_hasCompactSupport (hs _ (hw2 i)) (p := 1) }
  have hF : LocallyIntegrableOn D.operator (⊤ : Opens (Fin N → ℝ)) volume :=
    locallyIntegrableOn_of_locallyIntegrable_restrict (D.operator_memLp.locallyIntegrable le_rfl)
  refine ⟨hF, ?_⟩
  intro ψ
  have hb := D.ofFun_adjoint_equation le_rfl (fun i => (hX i).contDiffOn)
    D.operator Filter.EventuallyEq.rfl ψ
  rw [adjointTest_zero_eq_driftTransposeTest] at hb
  exact hb

end RothschildStein.H3
