-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Kernel.RepresentativeInitialCondition
public import HeatKernel.Kernel.DilationKernel

/-! # Conservation and initial limits from semigroup intertwining

Normalized L² dilation intertwining supplies pointwise kernel scaling.
Sub-Markov bounds and strong continuity then give conservation and the initial limit.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter
open scoped Topology
open RothschildStein

namespace HeatKernel

/-- Translation and dilation intertwining give a conservative sub-Markov representative kernel. -/
theorem integral_heatRepresentativeKernel_eq_one_of_submarkov_intertwining {n : ℕ}
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
    (hdilate : ∀ (r : ℝ) (hr : 0 < r), ∀ s, 0 < s → ∀ f,
      T s (dilationL2Equiv G hr f) = dilationL2Equiv G hr (T (r ^ 2 * s) f))
    (hstrong : ∀ f, Tendsto (fun t => T t f) (𝓝[>] 0) (𝓝 f))
    {t : ℝ} (ht : 0 < t) (x : Fin n → ℝ) :
    ∫ y, evaluationKernel (heatRepresentativeEvaluation T u hu hae) t x y = 1 := by
  have hscale (r t : ℝ) (hr : 0 < r) (ht : 0 < t) (x y : Fin n → ℝ) :
      evaluationKernel (heatRepresentativeEvaluation T u hu hae) (r ^ 2 * t)
        (G.dilate r x) (G.dilate r y) = (r ^ G.homogeneousDimension)⁻¹ *
          evaluationKernel (heatRepresentativeEvaluation T u hu hae) t x y :=
    heatRepresentativeKernel_parabolic_scaling G T u hu hae hr ht (hdilate r hr) x y
  exact integral_heatRepresentativeKernel_eq_one_of_submarkov_covariance
    G T u hu hae hself hsemigroup hjoint hpositive hmarkov hcomm hscale hstrong ht x

/-- Semigroup intertwining gives pointwise convergence against every bounded continuous test. -/
theorem tendsto_heatRepresentativeKernel_integral_of_submarkov_intertwining {n : ℕ}
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
    (hdilate : ∀ (r : ℝ) (hr : 0 < r), ∀ s, 0 < s → ∀ f,
      T s (dilationL2Equiv G hr f) = dilationL2Equiv G hr (T (r ^ 2 * s) f))
    (hstrong : ∀ f, Tendsto (fun t => T t f) (𝓝[>] 0) (𝓝 f))
    {φ : (Fin n → ℝ) → ℝ} (hφ : Continuous φ)
    (hbounded : ∃ C : ℝ, ∀ y, |φ y| ≤ C) (x : Fin n → ℝ) :
    Tendsto (fun t => ∫ y, evaluationKernel (heatRepresentativeEvaluation T u hu hae)
      t x y * φ y) (𝓝[>] 0) (𝓝 (φ x)) := by
  have hscale (r t : ℝ) (hr : 0 < r) (ht : 0 < t) (x y : Fin n → ℝ) :
      evaluationKernel (heatRepresentativeEvaluation T u hu hae) (r ^ 2 * t)
        (G.dilate r x) (G.dilate r y) = (r ^ G.homogeneousDimension)⁻¹ *
          evaluationKernel (heatRepresentativeEvaluation T u hu hae) t x y :=
    heatRepresentativeKernel_parabolic_scaling G T u hu hae hr ht (hdilate r hr) x y
  exact tendsto_heatRepresentativeKernel_integral_of_submarkov_covariance
    G T u hu hae hself hsemigroup hjoint hpositive hmarkov hcomm hscale hstrong hφ hbounded x

end HeatKernel
