-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Gaussian.ExponentialOperator
public import HeatKernel.Gaussian.WeightedEnergy
public import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Tactic

/-! # Energy trajectories for exponential conjugation

Strong continuity at time zero and positive-time derivatives pass through a
bounded exponential multiplier. The weighted inner-product inequality gives
the conjugated operator estimate by the energy growth argument.
-/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open MeasureTheory Set
namespace HeatKernel.Gaussian

/-- Continuous heat trajectories with a positive-time derivative and weighted
energy inequality give the exponential conjugation bound. -/
theorem norm_exponential_conjugation_le_of_energy {α : Type*} [MeasurableSpace α]
    (μ : Measure α) (ψ : α → ℝ) (hψ : AEStronglyMeasurable ψ μ) (B : ℝ)
    (hB : ∀ x, |ψ x| ≤ B) (T : ℝ → Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ)
    (D : Lp ℝ 2 μ → ℝ → Lp ℝ 2 μ) {a t : ℝ} (ht : 0 ≤ t)
    (hzero : T 0 = ContinuousLinearMap.id ℝ (Lp ℝ 2 μ))
    (hcont : ∀ f, ContinuousOn (fun s ↦ T s f) (Icc 0 t))
    (hderiv : ∀ f s, s ∈ Ioo 0 t → HasDerivAt (fun σ ↦ T σ f) (D f s) s)
    (henergy : ∀ f s, s ∈ Ioo 0 t →
      inner ℝ (exponentialMultiplication μ ψ hψ B hB a (T s f))
        (exponentialMultiplication μ ψ hψ B hB a (D f s)) ≤
          a ^ 2 * ‖exponentialMultiplication μ ψ hψ B hB a (T s f)‖ ^ 2) :
    ‖(exponentialMultiplication μ ψ hψ B hB a).comp
      ((T t).comp (exponentialMultiplication μ ψ hψ B hB (-a)))‖ ≤ Real.exp (a ^ 2 * t) := by
  let M := exponentialMultiplication μ ψ hψ B hB a
  let N := exponentialMultiplication μ ψ hψ B hB (-a)
  have hMN : M.comp N = ContinuousLinearMap.id ℝ (Lp ℝ 2 μ) :=
    exponentialMultiplication_comp_neg_eq_id μ ψ hψ B hB a
  apply opNorm_le_exp_of_energy_trajectories _
    (fun f s ↦ M (T s (N f))) (fun f s ↦ M (D (N f) s)) ht
  · intro f
    rw [hzero]
    exact congrArg (fun L : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ ↦ L f) hMN
  · intro f
    rfl
  · intro f
    exact M.continuous.comp_continuousOn (hcont (N f))
  · intro f s hs
    exact M.hasFDerivAt.comp_hasDerivAt s (hderiv (N f) s hs)
  · intro f s hs
    exact henergy (N f) s hs

end HeatKernel.Gaussian
