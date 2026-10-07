-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H1.BoundedFunctionalExtension
public import Mathlib.Analysis.Distribution.Distribution

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public section
noncomputable section
open TopologicalSpace
namespace RothschildStein.H1
variable {N : ℕ} (Ω : Opens (Fin N → ℝ))

/-- Hahn–Banach construction from the uniform transpose barrier
estimate on all smooth compact tests (BB Prop 6.2, p. 250).
The operator map P is the bounded continuous realization of the transpose;
this is the functional-analysis step, separate from the group barrier adapter. -/
theorem exists_orderZeroFunctional_of_barrier
    (P : TestFunction Ω ℝ (⊤ : ℕ∞) →ₗ[ℝ] BoundedContinuousFunction (Fin N → ℝ) ℝ)
    {C : ℝ} (hC : 0 ≤ C)
    (hbar : ∀ φ : TestFunction Ω ℝ (⊤ : ℕ∞),
      ‖(TestFunction.toBoundedContinuousFunctionCLM ℝ) φ‖ ≤ C * ‖P φ‖) :
    ∃ T : BoundedContinuousFunction (Fin N → ℝ) ℝ →L[ℝ] ℝ,
      ‖T‖ ≤ C ∧ ∀ φ : TestFunction Ω ℝ (⊤ : ℕ∞), T (P φ) = φ 0 := by
  let B : TestFunction Ω ℝ (⊤ : ℕ∞) →L[ℝ]
      BoundedContinuousFunction (Fin N → ℝ) ℝ := TestFunction.toBoundedContinuousFunctionCLM ℝ
  have hPinj : Function.Injective P := by
    intro φ ψ he
    have hn := hbar (φ - ψ)
    rw [P.map_sub, he, sub_self, norm_zero, mul_zero] at hn
    have hz : B (φ - ψ) = 0 := norm_eq_zero.mp (le_antisymm hn (norm_nonneg _))
    apply sub_eq_zero.mp
    apply TestFunction.injective_toBoundedContinuousFunctionCLM ℝ
    simpa only [map_zero] using hz
  let ev : TestFunction Ω ℝ (⊤ : ℕ∞) →ₗ[ℝ] ℝ :=
    (BoundedContinuousFunction.evalCLM (𝕜 := ℝ) (0 : Fin N → ℝ)).toLinearMap.comp B.toLinearMap
  have hb (φ : TestFunction Ω ℝ (⊤ : ℕ∞)) : ‖ev φ‖ ≤ C * ‖P φ‖ :=
    ((B φ).norm_coe_le_norm 0).trans (hbar φ)
  exact exists_boundedFunctional_extension P hPinj ev hC hb

/-- A bounded functional on Cb gives an order-zero distribution,
without a signed Riesz representation theorem (BB Prop 6.2, p. 250). -/
def orderZeroDistribution
    (T : BoundedContinuousFunction (Fin N → ℝ) ℝ →L[ℝ] ℝ) :
    Distribution Ω ℝ 0 :=
  T.comp (TestFunction.toBoundedContinuousFunctionCLM ℝ)

end RothschildStein.H1
