-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Kernel.KernelHeatEquation
public import HeatKernel.Kernel.SliceWeakHeatEquation
public import HeatKernel.Kernel.TwoSpaceSliceDerivatives

/-! # Kernel section identities for arbitrary two-space tests

Classical kernel sections can be tested against the restriction of an arbitrary
smooth compact two-space test. The derivative transfer identifies the resulting
integrand with the first spatial block of the full heat test.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped BigOperators

namespace HeatKernel

open RothschildStein

/-- A kernel section annihilates the first-block heat test at each fixed second endpoint. -/
theorem integral_kernel_section_twoSpace_heat_test_eq_zero {n q : ℕ}
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
    (hc : HasCompactSupport φ) (hs : tsupport φ ⊆ {z | 0 < z 0}) (y : Fin n → ℝ) :
    (∫ z in {z : Fin (1 + n) → ℝ | 0 < z 0},
      evaluationKernel (heatRepresentativeEvaluation T u hu hae)
        (timeSpaceCoordinates n z).1 (timeSpaceCoordinates n z).2 y *
      (fderiv ℝ φ (twoSpaceCoordinateSlice y z)
        (leftCoordinateInclusion 1 (n + n) (fun _ => 1)) +
        ∑ i : Fin q, fieldDerivative (liftRightField 1 (liftLeftField n (G.horizontalFields hq i)))
          (fieldDerivative (liftRightField 1 (liftLeftField n (G.horizontalFields hq i))) φ)
          (twoSpaceCoordinateSlice y z))) = 0 := by
  let v : (Fin (1 + n) → ℝ) → ℝ := fun z =>
    evaluationKernel (heatRepresentativeEvaluation T u hu hae)
      (timeSpaceCoordinates n z).1 (timeSpaceCoordinates n z).2 y
  have hv : ContDiffOn ℝ (⊤ : ℕ∞) v {z | 0 < z 0} :=
    (contDiffOn_heatRepresentativeKernel_other_section T u hu hae hself hsemigroup hsmooth y).comp
      (timeSpaceCoordinates n).contDiff.contDiffOn (fun z hz => hz)
  have hvheat : ∀ t, 0 < t → ∀ x,
      deriv (fun s => v ((timeSpaceCoordinates n).symm (s, x))) t =
        sumSquares (G.horizontalFields hq)
          (fun w => v ((timeSpaceCoordinates n).symm (t, w))) x := by
    intro t ht x
    simpa only [v, ContinuousLinearEquiv.apply_symm_apply] using
      deriv_heatRepresentativeKernel_eq_sumSquares_column (G.horizontalFields hq)
        T u hu hae hself hsemigroup hheat ht x y
  obtain ⟨hψ, hcψ, hsψ⟩ := smooth_compact_positive_twoSpace_test_slice φ hφ hc hs y
  have hw := integral_weak_heat_test_eq_zero_of_slice_equation G hq v hv hvheat
    (φ ∘ twoSpaceCoordinateSlice y) hψ hcψ hsψ
  have htest (z : Fin (1 + n) → ℝ) :
      fderiv ℝ (φ ∘ twoSpaceCoordinateSlice y) z (leftCoordinateInclusion 1 n (fun _ => 1)) +
        ∑ i : Fin q, fieldDerivative (liftRightField 1 (G.horizontalFields hq i))
          (fieldDerivative (liftRightField 1 (G.horizontalFields hq i))
            (φ ∘ twoSpaceCoordinateSlice y)) z =
      fderiv ℝ φ (twoSpaceCoordinateSlice y z)
        (leftCoordinateInclusion 1 (n + n) (fun _ => 1)) +
        ∑ i : Fin q, fieldDerivative (liftRightField 1 (liftLeftField n (G.horizontalFields hq i)))
          (fieldDerivative (liftRightField 1 (liftLeftField n (G.horizontalFields hq i))) φ)
          (twoSpaceCoordinateSlice y z) := by
    rw [fderiv_time_twoSpace_test_slice φ y z (hφ.differentiable (by simp)).differentiableAt]
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    exact fieldDerivative_sq_twoSpace_test_slice _ (G.horizontalFields_contDiff hq i) φ hφ y z
  simpa only [htest, v] using hw

end HeatKernel
