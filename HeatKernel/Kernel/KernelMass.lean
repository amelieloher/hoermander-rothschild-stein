-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Kernel.Conservation
public import HeatKernel.Kernel.KernelPairings

/-! # Excluding zero mass for representative kernels

A nonnegative integrable row of mass zero vanishes almost everywhere. The kernel
representation then forces the L² operator to vanish, which contradicts strong
continuity on any nonzero input when the mass identities force constant mass.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter
open scoped Topology

namespace HeatKernel

/-- Zero mass of nonnegative integrable rows forces every represented L² output to vanish. -/
theorem eq_zero_of_nonnegative_kernel_mass_zero {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (p : X → X → ℝ)
    (hpos : ∀ x y, 0 ≤ p x y) (hint : ∀ x, Integrable (p x) μ)
    (hmass : ∀ x, ∫ y, p x y ∂μ = 0) (f v : X → ℝ) (g : Lp ℝ 2 μ)
    (hrep : ∀ x, ∫ y, p x y * f y ∂μ = v x) (hae : g =ᵐ[μ] v) : g = 0 := by
  have hvzero (x : X) : v x = 0 := by
    rw [← hrep x]
    apply integral_eq_zero_of_ae
    filter_upwards [(integral_eq_zero_iff_of_nonneg (hpos x) (hint x)).mp (hmass x)] with y hy
    simp only [Pi.zero_apply, hy, zero_mul]
  apply Lp.ext
  filter_upwards [hae, Lp.coeFn_zero ℝ 2 μ] with x hx hz
  rw [hx, hvzero]
  simpa only [Pi.zero_apply] using hz.symm

variable {n : ℕ}
    (T : ℝ → Lp ℝ 2 (volume : Measure (Fin n → ℝ)) →L[ℝ]
      Lp ℝ 2 (volume : Measure (Fin n → ℝ)))
    (u : ℝ → Lp ℝ 2 (volume : Measure (Fin n → ℝ)) → (Fin n → ℝ) → ℝ)
    (hu : ∀ t, 0 < t → ∀ f, Continuous (u t f))
    (hae : ∀ t, 0 < t → ∀ f, T t f =ᵐ[volume] u t f)
    (hself : ∀ s, 0 ≤ s → IsSelfAdjoint (T s))
    (hsemigroup : ∀ s t, 0 ≤ s → 0 ≤ t → T (s + t) = (T s).comp (T t))

include hself hsemigroup

/-- Zero mass of all nonnegative kernel rows forces the positive-time operator to vanish. -/
theorem heatOperator_apply_eq_zero_of_kernel_mass_zero {t : ℝ} (ht : 0 < t)
    (hpos : ∀ x y, 0 ≤ evaluationKernel (heatRepresentativeEvaluation T u hu hae) t x y)
    (hint : ∀ x, Integrable (fun y =>
      evaluationKernel (heatRepresentativeEvaluation T u hu hae) t x y) volume)
    (hmass : ∀ x, ∫ y, evaluationKernel (heatRepresentativeEvaluation T u hu hae) t x y = 0)
    (f : Lp ℝ 2 (volume : Measure (Fin n → ℝ))) : T t f = 0 :=
  eq_zero_of_nonnegative_kernel_mass_zero volume
    (evaluationKernel (heatRepresentativeEvaluation T u hu hae) t) hpos hint hmass f (u t f) (T t f)
    (fun x => integral_heatRepresentativeKernel_mul_L2 T u hu hae hself hsemigroup ht x f)
    (hae t ht f)

/-- Common integrable row mass, scaling, composition, and strong continuity imply conservation. -/
theorem kernel_mass_eq_one_of_scaling_composition_and_strong_continuity
    (m : ℝ → ℝ)
    (hpos : ∀ t, 0 < t → ∀ x y,
      0 ≤ evaluationKernel (heatRepresentativeEvaluation T u hu hae) t x y)
    (hint : ∀ t, 0 < t → ∀ x, Integrable (fun y =>
      evaluationKernel (heatRepresentativeEvaluation T u hu hae) t x y) volume)
    (hmass : ∀ t, 0 < t → ∀ x,
      ∫ y, evaluationKernel (heatRepresentativeEvaluation T u hu hae) t x y = m t)
    (hscale : ∀ r t, 0 < r → 0 < t → m (r ^ 2 * t) = m t)
    (hadd : ∀ s t, 0 < s → 0 < t → m (s + t) = m s * m t)
    (hstrong : ∀ f, Tendsto (fun t => T t f) (𝓝[>] 0) (𝓝 f))
    (f : Lp ℝ 2 (volume : Measure (Fin n → ℝ))) (hf : f ≠ 0)
    {s : ℝ} (hs : 0 < s) : m s = 1 := by
  apply mass_eq_one_of_scaling_add_and_pairing m (fun t => inner ℝ f (T t f))
    hscale hadd (ne_of_gt (real_inner_self_pos.mpr hf)) (tendsto_const_nhds.inner (hstrong f)) ?_ hs
  intro t ht hmt
  have hz := heatOperator_apply_eq_zero_of_kernel_mass_zero T u hu hae hself hsemigroup ht
    (hpos t ht) (hint t ht) (fun x => (hmass t ht x).trans hmt) f
  rw [hz, inner_zero_right]

end HeatKernel
