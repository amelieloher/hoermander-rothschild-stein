-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import HeatKernel.Moser.MeanValueLinearTailTests
public import HeatKernel.Moser.WeakSolutionSpatialEnergy

/-! # Spatial cutoff formulas for the truncated-power energy test

The bounded spatial multiplier and the Lipschitz nonlinear composition act in
one zero-boundary graph. Their representatives give the precise principal and
mixed terms, with the chosen slope valid at exceptional truncation levels.
-/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

open Set MeasureTheory TopologicalSpace

namespace HeatKernel

/-- The actual square-cutoff power test has both the principal and cutoff-gradient
terms, using the selected slope even on exceptional scalar levels. -/
theorem caccioppoli_spatial_power_test_gradient_ae
    {N q : ℕ} {V : Opens (Fin N → ℝ)}
    {X : Fin q → (Fin N → ℝ) → (Fin N → ℝ)}
    (W : WeakSolutionSpatialWeight V X) (hX : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (X i))
    (ζ : (Fin N → ℝ) → ℝ) (d : Fin q → (Fin N → ℝ) → ℝ)
    (hW : ∀ᵐ x ∂volume, W.toFun x = ζ x ^ 2)
    (hd : ∀ i, ∀ᵐ x ∂volume, W.gradient i x = 2 * ζ x * d i x)
    {M p : ℝ} (hM : 0 < M) (hp : 2 ≤ p) (z : zeroBoundaryGraph V X) (i : Fin q) :
    (W.energyMap hX (linearTailPowerWeakSolutionTest hM (show 1 ≤ p - 1 by linarith)) z :
      GradientSpace (N := N) ⊤ q).snd i =ᵐ[volume] fun x =>
      ζ x ^ 2 * (linearTailPositivePowerSlope M (p - 1)
        ((z : GradientSpace (N := N) ⊤ q).fst x) *
        (z : GradientSpace (N := N) ⊤ q).snd i x) +
      (2 * ζ x * d i x) * linearTailPositivePower M (p - 1)
        ((z : GradientSpace (N := N) ⊤ q).fst x) := by
  let T := linearTailPowerWeakSolutionTest hM (show 1 ≤ p - 1 by linarith)
  have ht := linearTailPowerWeakSolutionTest_energyMap_ae V X hX hM
    (show 1 ≤ p - 1 by linarith) z
  filter_upwards [W.gradient_ae (T.energyMap V X hX z) i, ht.1, ht.2 i, hW, hd i]
    with x hx hv hg hw hdi
  exact hx.trans (by rw [hv, hg, hw, hdi])

end HeatKernel
