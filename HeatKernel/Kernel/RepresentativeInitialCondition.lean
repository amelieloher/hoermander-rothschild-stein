-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Kernel.SubmarkovConservation
public import HeatKernel.Kernel.DilationSubstitution

/-! # Pointwise initial condition for conservative representative kernels

The sub-Markov order properties give integrable rows, and covariance gives unit
mass and concentration of the time-one profile at every spatial center.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter
open scoped Topology

namespace HeatKernel

open RothschildStein

/-- The positive sub-Markov representative kernel converges against bounded continuous tests. -/
theorem tendsto_heatRepresentativeKernel_integral_of_submarkov_covariance {n : ℕ}
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
    {φ : (Fin n → ℝ) → ℝ} (hφ : Continuous φ)
    (hbounded : ∃ C : ℝ, ∀ y, |φ y| ≤ C) (x : Fin n → ℝ) :
    Tendsto (fun t => ∫ y, evaluationKernel (heatRepresentativeEvaluation T u hu hae)
      t x y * φ y) (𝓝[>] 0) (𝓝 (φ x)) := by
  obtain ⟨C, hC⟩ := hbounded
  have hpos (z w : Fin n → ℝ) :
      0 ≤ evaluationKernel (heatRepresentativeEvaluation T u hu hae) 1 z w :=
    heatRepresentativeKernel_nonneg T u hu hae hpositive 1 z w
  have hint := (integrable_heatRepresentativeKernel_row_of_submarkov T u hu hae
    hself hsemigroup hmarkov zero_lt_one hpos 0).1
  have hmass := integral_heatRepresentativeKernel_eq_one_of_submarkov_covariance
    G T u hu hae hself hsemigroup hjoint hpositive hmarkov hcomm hscale hstrong zero_lt_one 0
  exact tendsto_kernel_integral_of_covariance_and_unit_mass G
    (evaluationKernel (heatRepresentativeEvaluation T u hu hae))
    (fun t ht g z w => heatRepresentativeKernel_left_invariant G T u hu hae hcomm ht g z w)
    hscale hint hmass hφ (by simpa only [Real.norm_eq_abs] using hC) x

end HeatKernel
