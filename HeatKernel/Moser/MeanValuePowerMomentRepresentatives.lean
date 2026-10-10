-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Moser.MeanValuePowerEnergyRepresentatives
public import HeatKernel.Moser.MeanValueEnergyIntegrability
import Mathlib.Tactic

/-! # Literal power moments of localized half-power energy curves -/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set MeasureTheory TopologicalSpace
open scoped ENNReal
namespace HeatKernel

/-- On the support of a smaller cutoff the localized truncated half-power
is the same truncated half-power of the original solution. -/
theorem WeakSolutionSpatialWeight.localized_linearTail_half_power_value_ae {N q : ℕ}
    {V : Opens (Fin N → ℝ)} {X : Fin q → (Fin N → ℝ) → (Fin N → ℝ)}
    (W : WeakSolutionSpatialWeight V X) (hX : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (X i))
    {η φ f : (Fin N → ℝ) → ℝ} (hW : W.toFun =ᵐ[volume] η)
    (hplateau : ∀ x, η x ≠ 0 → φ x = 1)
    {M p : ℝ} (hM : 0 < M) (hp : 2 ≤ p) (z : zeroBoundaryGraph V X)
    (hf : (z : GradientSpace (N := N) ⊤ q).fst =ᵐ[volume] fun x => f x * φ x)
    (θ : ℝ) :
    ((θ • W.multiplier ((linearTailPowerWeakSolutionTest hM
      (show 1 ≤ p / 2 by linarith)).energyMap V X hX z) :
        zeroBoundaryGraph V X) : GradientSpace (N := N) ⊤ q).fst =ᵐ[volume]
      fun x => θ * η x * linearTailPositivePower M (p / 2) (f x) := by
  let H := (linearTailPowerWeakSolutionTest hM (show 1 ≤ p / 2 by linarith)).energyMap
    V X hX z
  have hs : (((θ • W.multiplier H : zeroBoundaryGraph V X) :
      GradientSpace (N := N) ⊤ q).fst) =ᵐ[volume]
        fun x => θ * (W.multiplier H : GradientSpace (N := N) ⊤ q).fst x := by
    simpa only [Submodule.coe_smul, WithLp.smul_fst, Pi.smul_def, smul_eq_mul,
      Opens.coe_top, Measure.restrict_univ] using
        Lp.coeFn_smul θ (W.multiplier H : GradientSpace (N := N) ⊤ q).fst
  filter_upwards [hs, W.value_ae H, hW, hf,
    (linearTailPowerWeakSolutionTest_energyMap_ae V X hX hM
      (show 1 ≤ p / 2 by linarith) z).1] with x hθ hw hη hfz hH
  dsimp only [H] at hθ hw
  rw [hθ, hw, hη, hH]
  by_cases hzero : η x = 0
  · simp only [hzero, zero_mul, mul_zero]
  · rw [hplateau x hzero, mul_one] at hfz
    rw [hfz]
    ring

end HeatKernel
