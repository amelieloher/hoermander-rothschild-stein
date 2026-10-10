-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Kernel.KernelConservation
public import HeatKernel.Kernel.SubmarkovRows
public import HeatKernel.Kernel.NonzeroL2
public import HeatKernel.Kernel.CountableEvaluations
public import HeatKernel.Kernel.L2Positivity

/-! # Conservation of positive sub-Markov representative kernels

The L² order properties give positive integrable kernel rows. Scalar continuity
gives joint measurability. Translation, dilation, and strong continuity then give
unit row mass at every positive time and every center.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter
open scoped Topology

namespace HeatKernel

open RothschildStein

/-- Positive sub-Markov semigroups with the stated group covariance have conservative kernels. -/
theorem integral_heatRepresentativeKernel_eq_one_of_submarkov_covariance {n : ℕ}
    (G : HomogeneousGroup n)
    (T : ℝ → Lp ℝ 2 (volume : Measure (Fin n → ℝ)) →L[ℝ]
      Lp ℝ 2 (volume : Measure (Fin n → ℝ)))
    (u : ℝ → Lp ℝ 2 (volume : Measure (Fin n → ℝ)) → (Fin n → ℝ) → ℝ)
    (hu : ∀ t, 0 < t → ∀ f, Continuous (u t f))
    (hae : ∀ t, 0 < t → ∀ f, T t f =ᵐ[volume] u t f)
    (hself : ∀ s, 0 ≤ s → IsSelfAdjoint (T s))
    (hsemigroup : ∀ s t, 0 ≤ s → 0 ≤ t → T (s + t) = (T s).comp (T t))
    (hjoint : ∀ f, ContinuousOn (fun p : ℝ × (Fin n → ℝ) => u p.1 f p.2)
      {p | 0 < p.1})
    (hpositive : ∀ t, 0 < t → ∀ f, (∀ᵐ x ∂volume, 0 ≤ f x) →
      ∀ᵐ x ∂volume, 0 ≤ T t f x)
    (hmarkov : ∀ t, 0 < t → ∀ f,
      (∀ᵐ x ∂volume, 0 ≤ f x ∧ f x ≤ 1) →
        ∀ᵐ x ∂volume, 0 ≤ T t f x ∧ T t f x ≤ 1)
    (hcomm : ∀ s, 0 < s → ∀ a f,
      T s (leftTranslationL2 G a f) = leftTranslationL2 G a (T s f))
    (hscale : ∀ r t, 0 < r → 0 < t → ∀ x y,
      evaluationKernel (heatRepresentativeEvaluation T u hu hae) (r ^ 2 * t)
        (G.dilate r x) (G.dilate r y) = (r ^ G.homogeneousDimension)⁻¹ *
          evaluationKernel (heatRepresentativeEvaluation T u hu hae) t x y)
    (hstrong : ∀ f, Tendsto (fun t => T t f) (𝓝[>] 0) (𝓝 f))
    {t : ℝ} (ht : 0 < t) (x : Fin n → ℝ) :
    ∫ y, evaluationKernel (heatRepresentativeEvaluation T u hu hae) t x y = 1 := by
  have hpos (s : ℝ) (_hs : 0 < s) (z w : Fin n → ℝ) :
      0 ≤ evaluationKernel (heatRepresentativeEvaluation T u hu hae) s z w :=
    heatRepresentativeKernel_nonneg T u hu hae hpositive s z w
  have hint (s : ℝ) (hs : 0 < s) (z : Fin n → ℝ) : Integrable
      (fun w => evaluationKernel (heatRepresentativeEvaluation T u hu hae) s z w) volume :=
    (integrable_heatRepresentativeKernel_row_of_submarkov T u hu hae hself hsemigroup hmarkov
      hs (hpos s hs) z).1
  have hmeas (s : ℝ) (_hs : 0 < s) : AEStronglyMeasurable
      (fun p : (Fin n → ℝ) × (Fin n → ℝ) =>
        evaluationKernel (heatRepresentativeEvaluation T u hu hae) s p.1 p.2)
      (volume.prod volume) :=
    ((measurable_heatRepresentativeKernel T u hu hae hjoint).comp
      (measurable_const.prodMk measurable_id)).aestronglyMeasurable
  obtain ⟨f, hf⟩ := exists_nonzero_euclidean_L2 n
  exact integral_heatRepresentativeKernel_eq_one_of_covariance_and_integrability G T u hu hae
    hself hsemigroup hpos hint hmeas hcomm hscale hstrong f hf ht x

end HeatKernel
