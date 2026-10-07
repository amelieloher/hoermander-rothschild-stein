-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H3.CoordinatePartialOne
public import RothschildStein.H3.C1FieldHomogeneity
public import Mathlib.LinearAlgebra.Pi

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
open Set
open scoped BigOperators
namespace RothschildStein.H3
variable {N : ℕ}

/-- A coordinate bound on a linear functional gives its
directional bound with the explicit coefficient sum. The coordinate
space keeps its original sup norm. -/
theorem linearFunctional_le_coordinate_sum (L : (Fin N → ℝ) →L[ℝ] ℝ)
    (v : Fin N → ℝ) {M : ℝ}
    (hM : ∀ j : Fin N, |L (Hormander.Interface.basisVec j)| ≤ M) :
    |L v| ≤ (∑ j : Fin N, |v j|) * M := by
  have hv : v = ∑ j : Fin N, v j • Hormander.Interface.basisVec j := by
    ext j
    simp [Hormander.Interface.basisVec, Pi.single_apply, Finset.sum_apply]
  conv_lhs => rw [hv, map_sum]
  calc
    _ ≤ ∑ j : Fin N, |L (v j • Hormander.Interface.basisVec j)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ j : Fin N, |v j| * M := by
      apply Finset.sum_le_sum
      intro j _
      rw [map_smul, smul_eq_mul, abs_mul]
      exact mul_le_mul_of_nonneg_left (hM j) (abs_nonneg _)
    _ = _ := (Finset.sum_mul _ _ _).symm

/-- Actual directional sphere maxima are controlled by Λ₁
and a constant depending only on the field's unit-sphere coefficients.
This avoids confusing Euclidean and sup norms in the shared coordinate type. -/
theorem fieldSphereBound_le_kernelDerivativeBound
    {G : HomogeneousGroup N} {ν T : (Fin N → ℝ) → ℝ}
    (hν : G.IsHomogeneousGauge ν) (hT : ContDiffOn ℝ (⊤ : ℕ∞) T {0}ᶜ)
    (V : (Fin N → ℝ) → (Fin N → ℝ)) (hV : ContinuousOn V {0}ᶜ) :
    kernelSphereBound ν (fieldDerivative V T) ≤
      kernelSphereBound ν (fun x => ∑ j : Fin N, |V x j|) *
        kernelDerivativeBound ν T 1 := by
  have hvsum : ContinuousOn (fun x => ∑ j : Fin N, |V x j|) {0}ᶜ := by
    apply continuousOn_finsetSum
    intro j _
    exact ((continuous_apply j).comp_continuousOn hV).abs
  obtain ⟨_, ⟨x, hx, he⟩, _⟩ := kernelSphereBound_continuous hν
    (fieldDerivative_continuousOn_C1 (hT.of_le (by simp)) hV)
  have hv := (kernelSphereBound_continuous hν hvsum).2.2 x hx
  have hsum : (∑ j : Fin N, |V x j|) ≤
      kernelSphereBound ν (fun x => ∑ j : Fin N, |V x j|) := by
    have hzero : 0 ≤ ∑ j : Fin N, |V x j| :=
      Finset.sum_nonneg (fun j _ => abs_nonneg _)
    rw [abs_of_nonneg hzero] at hv
    exact hv
  rw [← he]
  exact (linearFunctional_le_coordinate_sum (fderiv ℝ T x) (V x)
    (fun j => coordinate_derivative_le_kernelDerivativeBound hν hT j hx)).trans
      (mul_le_mul_of_nonneg_right hsum (kernelDerivativeBound_properties hν hT 1).1)

end RothschildStein.H3
