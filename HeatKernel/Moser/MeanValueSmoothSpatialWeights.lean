-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Moser.WeakSolutionSpatialWeights
public import HeatKernel.Form.SmoothCompactBoundaryMultipliers
import Mathlib.Tactic
import all Mathlib.Basic.Real.Basic

/-! # Smooth unit cutoffs as nonlinear energy weights -/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set MeasureTheory TopologicalSpace RothschildStein
namespace HeatKernel

/-- A smooth compact cutoff with values in the unit interval acts on the
zero-boundary graph, with its classical horizontal derivative as representative. -/
def WeakSolutionSpatialWeight.ofSmoothUnitCutoff {N q : ℕ}
    (V : Opens (Fin N → ℝ)) (X : Fin q → (Fin N → ℝ) → (Fin N → ℝ))
    (hX : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (X i))
    {η : (Fin N → ℝ) → ℝ} (hη : ContDiff ℝ (⊤ : ℕ∞) η)
    (hc : HasCompactSupport η) (hs : tsupport η ⊆ (V : Set (Fin N → ℝ)))
    (hunit : ∀ x, η x ∈ Icc (0 : ℝ) 1) : WeakSolutionSpatialWeight V X := by
  let hex := exists_smooth_compact_zeroBoundary_multiplier V X hX hη hc hs
  let M := Classical.choose hex
  have hM := Classical.choose_spec hex
  refine ⟨η, 1, hη.continuous.aestronglyMeasurable, ?_,
    fun i => fieldDerivative (X i) η, M.comp (zeroBoundaryEnergyInclusion V X), ?_, ?_⟩
  · exact Filter.Eventually.of_forall fun x => by
      simpa only [Real.norm_eq_abs, abs_of_nonneg (hunit x).1, NNReal.coe_one] using (hunit x).2
  · intro z
    exact (hM (zeroBoundaryEnergyInclusion V X z)).1
  · intro z i
    exact (hM (zeroBoundaryEnergyInclusion V X z)).2 i

/-- The classical horizontal derivative of a squared smooth cutoff retains
the exact factor two and the unsquared cutoff. -/
theorem fieldDerivative_smooth_cutoff_sq {N q : ℕ}
    (X : Fin q → (Fin N → ℝ) → (Fin N → ℝ))
    {η : (Fin N → ℝ) → ℝ} (hη : ContDiff ℝ (⊤ : ℕ∞) η) (i : Fin q) (x : Fin N → ℝ) :
    fieldDerivative (X i) (fun y => η y ^ 2) x =
      2 * η x * fieldDerivative (X i) η x := by
  have hdiff := (hη.differentiable (by simp)) x
  have he := S.fieldDerivative_mul (X i) η η x hdiff hdiff
  calc
    _ = fieldDerivative (X i) η x * η x + η x * fieldDerivative (X i) η x := by
      simpa only [pow_two] using he
    _ = _ := by ring

/-- Squaring a unit cutoff supplies the spatial weight and the exact gradient
required by the positive-power energy estimate. Both properties hold everywhere. -/
theorem exists_smooth_square_spatial_weight {N q : ℕ}
    (V : Opens (Fin N → ℝ)) (X : Fin q → (Fin N → ℝ) → (Fin N → ℝ))
    (hX : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (X i))
    {η : (Fin N → ℝ) → ℝ} (hη : ContDiff ℝ (⊤ : ℕ∞) η)
    (hc : HasCompactSupport η) (hs : tsupport η ⊆ (V : Set (Fin N → ℝ)))
    (hunit : ∀ x, η x ∈ Icc (0 : ℝ) 1) :
    ∃ W : WeakSolutionSpatialWeight V X,
      (∀ x, W.toFun x = η x ^ 2) ∧
      ∀ i x, W.gradient i x = 2 * η x * fieldDerivative (X i) η x := by
  have hsq : ∀ x, η x ^ 2 ∈ Icc (0 : ℝ) 1 := by
    intro x
    obtain ⟨h0, h1⟩ := hunit x
    exact ⟨sq_nonneg _, by nlinarith⟩
  have hcsq : HasCompactSupport (fun x => η x ^ 2) := by
    simpa only [pow_two, Pi.mul_def] using hc.mul_left (f := η)
  have hssq : tsupport (fun x => η x ^ 2) ⊆ (V : Set (Fin N → ℝ)) := by
    simpa only [pow_two] using (tsupport_mul_subset_left (f := η) (g := η)).trans hs
  let W := WeakSolutionSpatialWeight.ofSmoothUnitCutoff V X hX (hη.pow 2) hcsq hssq hsq
  refine ⟨W, fun _ => rfl, ?_⟩
  intro i x
  exact fieldDerivative_smooth_cutoff_sq X hη i x

end HeatKernel
