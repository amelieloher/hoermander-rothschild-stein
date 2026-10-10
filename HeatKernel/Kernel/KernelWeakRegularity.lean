-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Kernel.KernelHypoellipticity
public import HeatKernel.Kernel.CoordinateKernelIntegrability

/-! # Joint kernel smoothness from the literal two-space test identity

The representative kernel's local integrability follows from its compact
bounds. The remaining two-space test identity then supplies hypoellipticity.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped BigOperators

namespace HeatKernel

open Hormander.Interface RothschildStein

/-- The literal two-space heat-test identity gives joint smoothness of the representative kernel. -/
theorem contDiffOn_heatRepresentativeKernel_of_two_space_integral_identity {n q : ℕ}
    (G : HomogeneousGroup n) (hq : q ≤ n)
    (hspan : bracketSpansOn Set.univ (G.horizontalFields hq))
    (T : ℝ → Lp ℝ 2 (volume : Measure (Fin n → ℝ)) →L[ℝ]
      Lp ℝ 2 (volume : Measure (Fin n → ℝ)))
    (u : ℝ → Lp ℝ 2 (volume : Measure (Fin n → ℝ)) → (Fin n → ℝ) → ℝ)
    (hu : ∀ t, 0 < t → ∀ f, Continuous (u t f))
    (hae : ∀ t, 0 < t → ∀ f, T t f =ᵐ[volume] u t f)
    (hself : ∀ s, 0 ≤ s → IsSelfAdjoint (T s))
    (hsemigroup : ∀ s t, 0 ≤ s → 0 ≤ t → T (s + t) = (T s).comp (T t))
    (hsmooth : ∀ f, ContDiffOn ℝ (⊤ : ℕ∞)
      (fun p : ℝ × (Fin n → ℝ) => u p.1 f p.2) {p | 0 < p.1})
    (hweak : ∀ φ : (Fin (1 + (n + n)) → ℝ) → ℝ,
      ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ → tsupport φ ⊆ {x | 0 < x 0} →
      (∫ x in {x | 0 < x 0}, evaluationKernel (heatRepresentativeEvaluation T u hu hae)
        (timeTwoSpaceCoordinates n x).1 (timeTwoSpaceCoordinates n x).2.1
        (timeTwoSpaceCoordinates n x).2.2 *
        (2 * fderiv ℝ φ x (leftCoordinateInclusion 1 (n + n) (fun _ => 1)) +
          ∑ i : Fin (q + q), fderiv ℝ
            (fun y => fderiv ℝ φ y
              (liftRightField 1 (sumFields (G.horizontalFields hq) (G.horizontalFields hq) i) y)) x
            (liftRightField 1 (sumFields (G.horizontalFields hq) (G.horizontalFields hq) i) x))) = 0) :
    ContDiffOn ℝ (⊤ : ℕ∞)
      (fun p : (ℝ × (Fin n → ℝ)) × (Fin n → ℝ) =>
        evaluationKernel (heatRepresentativeEvaluation T u hu hae) p.1.1 p.1.2 p.2)
      ({p : ℝ × (Fin n → ℝ) | 0 < p.1} ×ˢ Set.univ) := by
  have hl := locallyIntegrableOn_coordinate_heatRepresentativeKernel T u hu hae
    (fun f => (hsmooth f).continuousOn)
  have hw := hasWeakHormanderEquation_horizontalTwoSpaceHeatFields_of_integral_identity
    G hq _ hl hweak
  exact contDiffOn_heatRepresentativeKernel_of_weak_two_space_equation
    G hq hspan T u hu hae hself hsemigroup hsmooth hw

end HeatKernel
