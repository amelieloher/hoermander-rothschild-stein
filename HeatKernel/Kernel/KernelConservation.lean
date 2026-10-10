-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Kernel.KernelMass
public import HeatKernel.Kernel.ProfileMass
public import HeatKernel.Kernel.MassComposition
public import HeatKernel.Kernel.L2KernelComposition

/-! # Conservation from covariance and integrable kernel rows

Translation and dilation give constant row mass under changes of center and positive
time. Kernel composition makes that mass idempotent. Strong L² continuity excludes
zero mass, giving conservation for the original kernel witness.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter
open scoped Topology

namespace HeatKernel

open RothschildStein

/-- Covariance, integrable positive rows, and strong continuity give unit mass everywhere. -/
theorem integral_heatRepresentativeKernel_eq_one_of_covariance_and_integrability {n : ℕ}
    (G : HomogeneousGroup n)
    (T : ℝ → Lp ℝ 2 (volume : Measure (Fin n → ℝ)) →L[ℝ]
      Lp ℝ 2 (volume : Measure (Fin n → ℝ)))
    (u : ℝ → Lp ℝ 2 (volume : Measure (Fin n → ℝ)) → (Fin n → ℝ) → ℝ)
    (hu : ∀ t, 0 < t → ∀ f, Continuous (u t f))
    (hae : ∀ t, 0 < t → ∀ f, T t f =ᵐ[volume] u t f)
    (hself : ∀ s, 0 ≤ s → IsSelfAdjoint (T s))
    (hsemigroup : ∀ s t, 0 ≤ s → 0 ≤ t → T (s + t) = (T s).comp (T t))
    (hpos : ∀ t, 0 < t → ∀ x y,
      0 ≤ evaluationKernel (heatRepresentativeEvaluation T u hu hae) t x y)
    (hint : ∀ t, 0 < t → ∀ x, Integrable (fun y =>
      evaluationKernel (heatRepresentativeEvaluation T u hu hae) t x y) volume)
    (hmeas : ∀ t, 0 < t → AEStronglyMeasurable
      (fun p : (Fin n → ℝ) × (Fin n → ℝ) =>
        evaluationKernel (heatRepresentativeEvaluation T u hu hae) t p.1 p.2)
      (volume.prod volume))
    (hcomm : ∀ s, 0 < s → ∀ a f,
      T s (leftTranslationL2 G a f) = leftTranslationL2 G a (T s f))
    (hscale : ∀ r t, 0 < r → 0 < t → ∀ x y,
      evaluationKernel (heatRepresentativeEvaluation T u hu hae) (r ^ 2 * t)
        (G.dilate r x) (G.dilate r y) = (r ^ G.homogeneousDimension)⁻¹ *
          evaluationKernel (heatRepresentativeEvaluation T u hu hae) t x y)
    (hstrong : ∀ f, Tendsto (fun t => T t f) (𝓝[>] 0) (𝓝 f))
    (f : Lp ℝ 2 (volume : Measure (Fin n → ℝ))) (hf : f ≠ 0)
    {t : ℝ} (ht : 0 < t) (x : Fin n → ℝ) :
    ∫ y, evaluationKernel (heatRepresentativeEvaluation T u hu hae) t x y = 1 := by
  let p := evaluationKernel (heatRepresentativeEvaluation T u hu hae)
  let m : ℝ → ℝ := fun s => ∫ y, p s 0 y
  have hmass (s : ℝ) (hs : 0 < s) (z : Fin n → ℝ) : ∫ y, p s z y = m s :=
    integral_heatRepresentativeKernel_row_eq_profile G T u hu hae hcomm hs z
  have hscaleMass : ∀ r s, 0 < r → 0 < s → m (r ^ 2 * s) = m s := by
    intro r s hr hs
    exact integral_kernel_profile_parabolic_scaling G p hscale hr hs
  have hadd : ∀ s v, 0 < s → 0 < v → m (s + v) = m s * m v := by
    intro s v hs hv
    exact mass_composition_of_integrable_nonnegative_kernels volume
      (p s) (p v) (p (s + v)) (m s) (m v) (m (s + v))
      (hpos s hs) (hpos v hv) (hint s hs) (hint v hv) (hmeas v hv)
      (hmass s hs) (hmass v hv) (hmass (s + v) (add_pos hs hv))
      (fun z w => integral_heatRepresentativeKernel_mul T u hu hae hself hsemigroup hs hv z w) 0
  exact (hmass t ht x).trans
    (kernel_mass_eq_one_of_scaling_composition_and_strong_continuity T u hu hae hself hsemigroup
      m hpos hint hmass hscaleMass hadd hstrong f hf ht)

end HeatKernel
