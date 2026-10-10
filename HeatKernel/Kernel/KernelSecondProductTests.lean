-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Kernel.KernelProductTests
public import HeatKernel.Kernel.TwoSpaceSwapDerivatives

/-! # The second spatial product weak heat identity

Spatial exchange preserves positive-time measure and the symmetric kernel.
Applying the first product identity to the exchanged test gives the second.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter
open scoped BigOperators

namespace HeatKernel

open RothschildStein

/-- Spatial exchange transfers the first product weak heat identity to the second block. -/
theorem integral_kernel_twoSpace_second_heat_test_eq_zero {n q : ℕ}
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
        ∑ i : Fin q, fieldDerivative (liftRightField 1 (liftRightField n (G.horizontalFields hq i)))
          (fieldDerivative (liftRightField 1 (liftRightField n (G.horizontalFields hq i))) φ) z)) = 0 := by
  let ψ := φ ∘ twoSpaceSwap n
  have hψ : ContDiff ℝ (⊤ : ℕ∞) ψ := hφ.comp (twoSpaceSwap n).contDiff
  have hcψ : HasCompactSupport ψ := hc.comp_isClosedEmbedding (twoSpaceSwap n).toHomeomorph.isClosedEmbedding
  have hsψ : tsupport ψ ⊆ {z | 0 < z 0} := by
    intro z hz
    have h := hs (tsupport_comp_subset_preimage φ (twoSpaceSwap n).continuous hz)
    simpa only [Set.mem_ofPred_eq, twoSpaceSwap_time] using h
  have hfirst := integral_kernel_twoSpace_first_heat_test_eq_zero G hq T u hu hae hself hsemigroup
    hsmooth hheat ψ hψ hcψ hsψ
  let F : (Fin (1 + (n + n)) → ℝ) → ℝ := fun z =>
    evaluationKernel (heatRepresentativeEvaluation T u hu hae)
      (timeTwoSpaceCoordinates n z).1 (timeTwoSpaceCoordinates n z).2.1
      (timeTwoSpaceCoordinates n z).2.2 *
      (fderiv ℝ φ z (leftCoordinateInclusion 1 (n + n) (fun _ => 1)) +
        ∑ i : Fin q, fieldDerivative (liftRightField 1 (liftRightField n (G.horizontalFields hq i)))
          (fieldDerivative (liftRightField 1 (liftRightField n (G.horizontalFields hq i))) φ) z)
  have htest (z : Fin (1 + (n + n)) → ℝ) :
      fderiv ℝ ψ z (leftCoordinateInclusion 1 (n + n) (fun _ => 1)) +
        ∑ i : Fin q, fieldDerivative (liftRightField 1 (liftLeftField n (G.horizontalFields hq i)))
          (fieldDerivative (liftRightField 1 (liftLeftField n (G.horizontalFields hq i))) ψ) z =
      fderiv ℝ φ (twoSpaceSwap n z) (leftCoordinateInclusion 1 (n + n) (fun _ => 1)) +
        ∑ i : Fin q, fieldDerivative (liftRightField 1 (liftRightField n (G.horizontalFields hq i)))
          (fieldDerivative (liftRightField 1 (liftRightField n (G.horizontalFields hq i))) φ)
          (twoSpaceSwap n z) := by
    rw [fderiv_time_comp_twoSpaceSwap φ z (hφ.differentiable (by simp)).differentiableAt]
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    exact fieldDerivative_sq_first_comp_twoSpaceSwap _ (G.horizontalFields_contDiff hq i) φ hφ z
  have hkernel (z : Fin (1 + (n + n)) → ℝ) :
      evaluationKernel (heatRepresentativeEvaluation T u hu hae)
        (timeTwoSpaceCoordinates n (twoSpaceSwap n z)).1
        (timeTwoSpaceCoordinates n (twoSpaceSwap n z)).2.1
        (timeTwoSpaceCoordinates n (twoSpaceSwap n z)).2.2 =
      evaluationKernel (heatRepresentativeEvaluation T u hu hae)
        (timeTwoSpaceCoordinates n z).1 (timeTwoSpaceCoordinates n z).2.1
        (timeTwoSpaceCoordinates n z).2.2 := by
    rw [timeTwoSpaceCoordinates_twoSpaceSwap]
    exact evaluationKernel_symm _ _ _ _
  have hcomp (z : Fin (1 + (n + n)) → ℝ) : F (twoSpaceSwap n z) =
      evaluationKernel (heatRepresentativeEvaluation T u hu hae)
        (timeTwoSpaceCoordinates n z).1 (timeTwoSpaceCoordinates n z).2.1
        (timeTwoSpaceCoordinates n z).2.2 *
      (fderiv ℝ ψ z (leftCoordinateInclusion 1 (n + n) (fun _ => 1)) +
        ∑ i : Fin q, fieldDerivative (liftRightField 1 (liftLeftField n (G.horizontalFields hq i)))
          (fieldDerivative (liftRightField 1 (liftLeftField n (G.horizontalFields hq i))) ψ) z) := by
    dsimp only [F]
    rw [hkernel, ← htest]
  have hi : (∫ z in {z : Fin (1 + (n + n)) → ℝ | 0 < z 0}, F (twoSpaceSwap n z)) = 0 := by
    simpa only [hcomp] using hfirst
  exact ((measurePreserving_twoSpaceSwap_positive n).integral_comp
    (twoSpaceSwap n).toHomeomorph.measurableEmbedding F).symm.trans hi

end HeatKernel
