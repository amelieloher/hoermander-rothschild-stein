-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Gaussian.SmoothHorizontalKernel
import Mathlib.Tactic

/-! # Sums of squares under compact-data kernel integrals

Joint second-order regularity makes every second horizontal derivative
integrable and permits the full sum-of-squares operator to pass through the
compact-data integral.
-/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open MeasureTheory Set RothschildStein
open scoped BigOperators
namespace HeatKernel.Gaussian

/-- The horizontal sum of squares commutes with compact-data integration for a
jointly second-order kernel and first-order vector fields. -/
theorem sumSquares_kernel_integral_of_contDiff {N q : ℕ} {Z : Type*}
    [NormedAddCommGroup Z] [NormedSpace ℝ Z] [MeasurableSpace Z]
    [BorelSpace Z] [SecondCountableTopology Z]
    (μ : Measure Z) {f : Z → ℝ} (hf : Integrable f μ)
    {K : Set Z} (hK : IsCompact K) (hsupp : Function.support f ⊆ K)
    {U : Set (Fin N → ℝ)} (hU : IsOpen U) {x : Fin N → ℝ} (hx : x ∈ U)
    (k : (Fin N → ℝ) × Z → ℝ) (hk : ContDiffOn ℝ 2 k (U ×ˢ univ))
    (X : Fin q → (Fin N → ℝ) → (Fin N → ℝ))
    (hX : ∀ i, ContDiffOn ℝ 1 (X i) U) :
    sumSquares X (fun y ↦ ∫ z, f z * k (y, z) ∂μ) x =
      ∫ z, f z * sumSquares X (fun y ↦ k (y, z)) x ∂μ := by
  unfold sumSquares
  calc
    _ = ∑ i, ∫ z, f z * fieldDerivative (X i) (fieldDerivative (X i) (fun y ↦ k (y, z))) x ∂μ := by
      apply Finset.sum_congr rfl
      intro i _
      exact fieldDerivative_fieldDerivative_kernel_integral_of_contDiff μ hf hK hsupp hU hx
        k hk (X i) (X i) (hX i)
    _ = ∫ z, ∑ i, f z * fieldDerivative (X i) (fieldDerivative (X i) (fun y ↦ k (y, z))) x ∂μ :=
      (integral_finsetSum _ (fun i _ ↦ integrable_second_fieldDerivative_kernel_of_contDiff
        μ hf hK hsupp hU hx k hk (X i) (X i) (hX i))).symm
    _ = _ := by simp only [Finset.mul_sum]

end HeatKernel.Gaussian
