-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Kernel.KernelPairings
public import Mathlib.Analysis.InnerProductSpace.Continuous

/-! # Strong initial convergence of kernel integrals

The integral representation identifies the kernel evolution with its semigroup
class in L². Strong continuity gives convergence of the explicit integral error.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter
open scoped Topology

namespace HeatKernel

variable {n : ℕ}
    (T : ℝ → Lp ℝ 2 (volume : Measure (Fin n → ℝ)) →L[ℝ]
      Lp ℝ 2 (volume : Measure (Fin n → ℝ)))
    (u : ℝ → Lp ℝ 2 (volume : Measure (Fin n → ℝ)) → (Fin n → ℝ) → ℝ)
    (hu : ∀ t, 0 < t → ∀ f, Continuous (u t f))
    (hae : ∀ t, 0 < t → ∀ f, T t f =ᵐ[volume] u t f)
    (hself : ∀ s, 0 ≤ s → IsSelfAdjoint (T s))
    (hsemigroup : ∀ s t, 0 ≤ s → 0 ≤ t → T (s + t) = (T s).comp (T t))

include hself hsemigroup

/-- The kernel integral represents the semigroup class almost everywhere. -/
theorem ae_integral_heatRepresentativeKernel_mul_L2 {t : ℝ} (ht : 0 < t)
    (f : Lp ℝ 2 (volume : Measure (Fin n → ℝ))) :
    (fun x => ∫ y, evaluationKernel (heatRepresentativeEvaluation T u hu hae) t x y * f y)
      =ᵐ[volume] T t f := by
  filter_upwards [hae t ht f] with x hx
  rw [integral_heatRepresentativeKernel_mul_L2 T u hu hae hself hsemigroup ht x f, hx]

/-- The L² size of the integral error equals the semigroup error norm. -/
theorem eLpNorm_integral_heatRepresentativeKernel_sub_L2 {t : ℝ} (ht : 0 < t)
    (f : Lp ℝ 2 (volume : Measure (Fin n → ℝ))) :
    eLpNorm (fun x => (∫ y,
      evaluationKernel (heatRepresentativeEvaluation T u hu hae) t x y * f y) - f x)
      2 volume = ‖T t f - f‖ₑ := by
  rw [Lp.enorm_def]
  apply eLpNorm_congr_ae
  filter_upwards [ae_integral_heatRepresentativeKernel_mul_L2 T u hu hae hself hsemigroup ht f,
    Lp.coeFn_sub (T t f) f] with x hx hs
  exact hx ▸ hs.symm

/-- Strong semigroup continuity gives L² convergence of the kernel integral to its datum. -/
theorem tendsto_eLpNorm_integral_heatRepresentativeKernel_sub_L2
    (hstrong : ∀ f, Tendsto (fun t => T t f) (𝓝[>] 0) (𝓝 f))
    (f : Lp ℝ 2 (volume : Measure (Fin n → ℝ))) :
    Tendsto (fun t => eLpNorm (fun x => (∫ y,
      evaluationKernel (heatRepresentativeEvaluation T u hu hae) t x y * f y) - f x)
      2 volume) (𝓝[>] 0) (𝓝 0) := by
  have hlim : Tendsto (fun t => ‖T t f - f‖ₑ) (𝓝[>] 0) (𝓝 0) := by
    simpa only [sub_self, enorm_zero] using ((hstrong f).sub (tendsto_const_nhds (x := f))).enorm
  apply hlim.congr'
  filter_upwards [self_mem_nhdsWithin] with t ht
  exact (eLpNorm_integral_heatRepresentativeKernel_sub_L2 T u hu hae hself hsemigroup ht f).symm

end HeatKernel
