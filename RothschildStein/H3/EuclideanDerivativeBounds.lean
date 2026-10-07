-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H3.CoordinatePartialOne
public import Mathlib.Analysis.InnerProductSpace.Dual

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public section
noncomputable section
open Set
open scoped BigOperators
namespace RothschildStein.H3
variable {N : ℕ}

/-- The fixed coordinate transfer to the Euclidean norm. -/
def coordinateEuclideanEquiv (N : ℕ) :
    EuclideanSpace ℝ (Fin N) ≃L[ℝ] (Fin N → ℝ) :=
  PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin N => ℝ)

/-- The coordinate differential with the Euclidean norm on
its input, whose norm is the Euclidean gradient norm. -/
def euclideanDifferential (f : (Fin N → ℝ) → ℝ) (x : Fin N → ℝ) :
    EuclideanSpace ℝ (Fin N) →L[ℝ] ℝ :=
  (fderiv ℝ f x).comp (coordinateEuclideanEquiv N).toContinuousLinearMap

/-- Coordinate bounds control the Euclidean functional norm
with the precise square-root dimension factor, by the orthonormal basis
sum-of-squares identity. -/
theorem euclideanFunctional_norm_le {M : ℝ} (hM : 0 ≤ M)
    (L : EuclideanSpace ℝ (Fin N) →L[ℝ] ℝ)
    (h : ∀ i : Fin N, |L (EuclideanSpace.basisFun (Fin N) ℝ i)| ≤ M) :
    ‖L‖ ≤ Real.sqrt N * M := by
  have hs : ‖L‖ ^ 2 ≤ (N : ℝ) * M ^ 2 := by
    rw [(EuclideanSpace.basisFun (Fin N) ℝ).norm_dual L]
    calc
      _ ≤ ∑ _ : Fin N, M ^ 2 := by
        apply Finset.sum_le_sum
        intro i _
        have hi := h i
        nlinarith [abs_nonneg (L (EuclideanSpace.basisFun (Fin N) ℝ i)),
          sq_abs (L (EuclideanSpace.basisFun (Fin N) ℝ i))]
      _ = _ := by simp
  have hsq := Real.sq_sqrt (show (0 : ℝ) ≤ N by positivity)
  have hnon : 0 ≤ Real.sqrt N * M := mul_nonneg (Real.sqrt_nonneg _) hM
  nlinarith [norm_nonneg L]

/-- The actual Euclidean gradient norm on the unit sphere is
bounded by sqrt(N) times the shared finite derivative maximum Λ₁. -/
theorem euclideanDifferential_norm_le_kernelDerivativeBound
    {G : HomogeneousGroup N} {ν T : (Fin N → ℝ) → ℝ}
    (hν : G.IsHomogeneousGauge ν) (hT : ContDiffOn ℝ (⊤ : ℕ∞) T {0}ᶜ)
    {x : Fin N → ℝ} (hx : ν x = 1) :
    ‖euclideanDifferential T x‖ ≤ Real.sqrt N * kernelDerivativeBound ν T 1 := by
  apply euclideanFunctional_norm_le (kernelDerivativeBound_properties hν hT 1).1
  intro i
  have hi := coordinate_derivative_le_kernelDerivativeBound hν hT i hx
  have he : coordinateEuclideanEquiv N (EuclideanSpace.basisFun (Fin N) ℝ i) =
      Hormander.Interface.basisVec i := by
    ext j
    simp [coordinateEuclideanEquiv, EuclideanSpace.basisFun_apply,
      Hormander.Interface.basisVec, Pi.single_apply]
  simpa only [euclideanDifferential, ContinuousLinearMap.comp_apply,
    ContinuousLinearEquiv.coe_coe, he] using hi

end RothschildStein.H3
