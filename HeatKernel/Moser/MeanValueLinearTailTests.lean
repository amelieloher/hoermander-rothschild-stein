-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Moser.MeanValueLinearTailDerivatives
public import HeatKernel.Moser.WeakSolutionEnergyTesting
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import all Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Tactic

/-! # Linear-tail positive powers in the nonlinear weak test interface -/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set MeasureTheory TopologicalSpace RothschildStein
namespace HeatKernel

/-- The positive-power energy test with a linear upper tail. -/
def linearTailPowerWeakSolutionTest {M γ : ℝ} (hM : 0 < M) (hγ : 1 ≤ γ) :
    WeakSolutionScalarTest where
  toFun := linearTailPositivePower M γ
  bound := Real.toNNReal (γ * M ^ (γ - 1)) + ‖M ^ (γ - 1)‖₊
  lipschitz := lipschitzWith_linearTailPositivePower hM.le hγ
  map_zero := linearTailPositivePower_zero hM.le (zero_lt_one.trans_le hγ)
  exceptional := {0, M}
  countable_exceptional := (countable_singleton M).insert 0
  contDiffAt := by
    intro s hs
    have hn : s ≠ 0 ∧ s ≠ M := by
      simpa only [mem_insert_iff, mem_singleton_iff, not_or] using hs
    exact contDiffAt_linearTailPositivePower hn.1 hn.2

/-- At energy exponent p, the test is exactly s min(s,M)^(p−2) for nonnegative s. -/
theorem linearTailPowerWeakSolutionTest_apply_power {M p s : ℝ}
    (hM : 0 < M) (hp : 2 ≤ p) (hs : 0 ≤ s) :
    (linearTailPowerWeakSolutionTest hM (show 1 ≤ p - 1 by linarith)).toFun s =
      s * (min s M) ^ (p - 2) := by
  change linearTailPositivePower M (p - 1) s = _
  have he : p - 1 - 1 = p - 2 := by ring
  simpa only [he] using
    linearTailPositivePower_eq_mul_min_rpow hM (show 1 ≤ p - 1 by linarith) hs

/-- Below the threshold, the normalized primitive is the exact power energy. -/
theorem linearTailPowerWeakSolutionTest_primitive {M γ s : ℝ}
    (hM : 0 < M) (hγ : 1 ≤ γ) (hs : 0 ≤ s) (hsM : s ≤ M) :
    (linearTailPowerWeakSolutionTest hM hγ).primitive s = s ^ (γ + 1) / (γ + 1) := by
  change (∫ t in (0 : ℝ)..s, linearTailPositivePower M γ t) = _
  calc
    _ = ∫ t in (0 : ℝ)..s, t ^ γ := by
      apply intervalIntegral.integral_congr
      intro t ht
      rw [uIcc_of_le hs] at ht
      exact linearTailPositivePower_eq_rpow ht.1 (ht.2.trans hsM)
    _ = (s ^ (γ + 1) - (0 : ℝ) ^ (γ + 1)) / (γ + 1) :=
      integral_rpow (Or.inl (by linarith))
    _ = _ := by rw [Real.zero_rpow (by linarith : γ + 1 ≠ 0), sub_zero]

/-- The common energy map has the literal test value and its exact chain factor,
including both exceptional level sets. -/
theorem linearTailPowerWeakSolutionTest_energyMap_ae {N q : ℕ}
    (V : Opens (Fin N → ℝ)) (X : Fin q → (Fin N → ℝ) → (Fin N → ℝ))
    (hX : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (X i)) {M γ : ℝ}
    (hM : 0 < M) (hγ : 1 ≤ γ) (u : zeroBoundaryGraph V X) :
    ((linearTailPowerWeakSolutionTest hM hγ).energyMap V X hX u :
      GradientSpace (N := N) ⊤ q).fst =ᵐ[volume]
        (fun x => linearTailPositivePower M γ ((u : GradientSpace (N := N) ⊤ q).fst x)) ∧
    ∀ i, ((linearTailPowerWeakSolutionTest hM hγ).energyMap V X hX u :
      GradientSpace (N := N) ⊤ q).snd i =ᵐ[volume]
        (fun x => linearTailPositivePowerSlope M γ ((u : GradientSpace (N := N) ⊤ q).fst x) *
          (u : GradientSpace (N := N) ⊤ q).snd i x) := by
  let T := linearTailPowerWeakSolutionTest hM hγ
  let v := zeroBoundaryEnergyInclusion V X u
  let z := piecewiseEnergyComposition X hX T.lipschitz T.map_zero
    T.exceptional T.countable_exceptional T.contDiffAt v
  have hf := piecewiseEnergyComposition_fst_ae X hX T.lipschitz T.map_zero
    T.exceptional T.countable_exceptional T.contDiffAt v
  have hd : ∀ s ∉ T.exceptional,
      linearTailPositivePowerSlope M γ s = deriv T.toFun s := by
    intro s hs
    have hn : s ≠ 0 ∧ s ≠ M := by
      simpa only [T, linearTailPowerWeakSolutionTest, mem_insert_iff,
        mem_singleton_iff, not_or] using hs
    exact linearTailPositivePowerSlope_eq_deriv hM hγ hn.1 hn.2
  refine ⟨hf, ?_⟩
  intro i
  exact energyGraph_chainRule_contDiffAt_off_countable X hX v z hf
    T.exceptional T.countable_exceptional T.contDiffAt hd i

end HeatKernel
