-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Kernel.KernelSectionTests
public import HeatKernel.Kernel.CoordinateKernelIntegrability
public import HeatKernel.Kernel.OperatorTestIntegrability

/-! # Product weak heat testing from classical kernel sections

Compact test integrability permits Fubini. Integrating the fixed-endpoint
section identities gives the first spatial block of the full weak heat equation.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped BigOperators

namespace HeatKernel

open RothschildStein

/-- The classical section equation gives the first-block product weak heat identity. -/
theorem integral_kernel_twoSpace_first_heat_test_eq_zero {n q : ℕ}
    (G : HomogeneousGroup n) (hq : q ≤ n)
    (T : ℝ → Lp ℝ 2 (volume : Measure (Fin n → ℝ)) →L[ℝ]
      Lp ℝ 2 (volume : Measure (Fin n → ℝ)))
    (u : ℝ → Lp ℝ 2 (volume : Measure (Fin n → ℝ)) → (Fin n → ℝ) → ℝ)
    (hu : ∀ t, 0 < t → ∀ f, Continuous (u t f))
    (hae : ∀ t, 0 < t → ∀ f, T t f =ᵐ[volume] u t f)
    (hself : ∀ s, 0 ≤ s → IsSelfAdjoint (T s))
    (hsemigroup : ∀ s t, 0 ≤ s → 0 ≤ t → T (s + t) = (T s).comp (T t))
    (hsmooth : ∀ f, ContDiffOn ℝ (⊤ : ℕ∞)
      (fun p : ℝ × (Fin n → ℝ) => u p.1 f p.2) {p | 0 < p.1})
    (hheat : ∀ t, 0 < t → ∀ f x, deriv (fun s => u s f x) t =
      sumSquares (G.horizontalFields hq) (u t f) x)
    (φ : (Fin (1 + (n + n)) → ℝ) → ℝ) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hc : HasCompactSupport φ) (hs : tsupport φ ⊆ {z | 0 < z 0}) :
    (∫ z in {z : Fin (1 + (n + n)) → ℝ | 0 < z 0},
      evaluationKernel (heatRepresentativeEvaluation T u hu hae)
        (timeTwoSpaceCoordinates n z).1 (timeTwoSpaceCoordinates n z).2.1
        (timeTwoSpaceCoordinates n z).2.2 *
      (fderiv ℝ φ z (leftCoordinateInclusion 1 (n + n) (fun _ => 1)) +
        ∑ i : Fin q, fieldDerivative (liftRightField 1 (liftLeftField n (G.horizontalFields hq i)))
          (fieldDerivative (liftRightField 1 (liftLeftField n (G.horizontalFields hq i))) φ) z)) = 0 := by
  let X := timeSpaceFields 1 (fun i : Fin q => liftLeftField n (G.horizontalFields hq i))
  let F : (Fin (1 + (n + n)) → ℝ) → ℝ := fun z =>
    evaluationKernel (heatRepresentativeEvaluation T u hu hae)
      (timeTwoSpaceCoordinatesAssoc n z).1.1 (timeTwoSpaceCoordinatesAssoc n z).1.2
      (timeTwoSpaceCoordinatesAssoc n z).2 * sumSquaresWithDrift X φ z
  have hX : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (X i) :=
    contDiff_timeSpaceFields 1 _ (fun i => (G.horizontalFields_contDiff hq i).liftLeftField n)
  have hint : Integrable F volume := integrable_mul_sumSquaresWithDrift_compact_test
    (locallyIntegrableOn_coordinate_heatRepresentativeKernel T u hu hae
      (fun f => (hsmooth f).continuousOn)) X hX φ hφ hc hs
  let μ : Measure (ℝ × (Fin n → ℝ)) := volume.restrict {p | 0 < p.1}
  have hp := measurePreserving_timeTwoSpaceCoordinatesAssoc_positive n
  have hpi := MeasurePreserving.symm (timeTwoSpaceCoordinatesAssoc n).toHomeomorph.toMeasurableEquiv hp
  have hprod : Integrable (fun p => F ((timeTwoSpaceCoordinatesAssoc n).symm p))
      (μ.prod volume) := hpi.integrable_comp_of_integrable hint.integrableOn
  have hp1 : MeasurePreserving (timeSpaceCoordinates n)
      (volume.restrict {z : Fin (1 + n) → ℝ | 0 < z 0}) μ :=
    (measurePreserving_timeSpaceCoordinates n).restrict_preimage_emb
      (timeSpaceCoordinates n).toHomeomorph.measurableEmbedding {p | 0 < p.1}
  have hsection (y : Fin n → ℝ) :
      (∫ p, F ((timeTwoSpaceCoordinatesAssoc n).symm (p, y)) ∂μ) = 0 := by
    rw [← hp1.integral_comp (timeSpaceCoordinates n).toHomeomorph.measurableEmbedding
      (fun p => F ((timeTwoSpaceCoordinatesAssoc n).symm (p, y)))]
    have h := integral_kernel_section_twoSpace_heat_test_eq_zero G hq T u hu hae
      hself hsemigroup hsmooth hheat φ hφ hc hs y
    simpa only [F, X, sumSquaresWithDrift, timeSpaceFields_zero, timeSpaceFields_succ,
      fieldDerivative, twoSpaceCoordinateSlice, ContinuousLinearEquiv.apply_symm_apply] using h
  have hzero : (∫ z in {z : Fin (1 + (n + n)) → ℝ | 0 < z 0}, F z) = 0 := by
    rw [← hpi.integral_comp (timeTwoSpaceCoordinatesAssoc n).symm.toHomeomorph.measurableEmbedding F]
    change (∫ p, F ((timeTwoSpaceCoordinatesAssoc n).symm p) ∂μ.prod volume) = 0
    rw [integral_prod_symm _ hprod]
    simp only [hsection, integral_zero]
  have hassoc (z : Fin (1 + (n + n)) → ℝ) : timeTwoSpaceCoordinatesAssoc n z =
      (((timeTwoSpaceCoordinates n z).1, (timeTwoSpaceCoordinates n z).2.1),
        (timeTwoSpaceCoordinates n z).2.2) := by
    change (ContinuousLinearEquiv.prodAssoc ℝ ℝ (Fin n → ℝ) (Fin n → ℝ)).symm
      (timeTwoSpaceCoordinates n z) = _
    simpa only [Prod.mk.eta] using ContinuousLinearEquiv.prodAssoc_symm_apply
      ℝ ℝ (Fin n → ℝ) (Fin n → ℝ) (timeTwoSpaceCoordinates n z).1
        (timeTwoSpaceCoordinates n z).2.1 (timeTwoSpaceCoordinates n z).2.2
  simpa only [F, X, sumSquaresWithDrift, timeSpaceFields_zero, timeSpaceFields_succ,
    fieldDerivative, hassoc] using hzero

end HeatKernel
