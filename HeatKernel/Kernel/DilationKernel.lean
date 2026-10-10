-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Kernel.DilationUnitary
public import HeatKernel.Kernel.RepresentativeCovariance

/-! # Pointwise parabolic covariance of the representative kernel

The normalized L² dilation action turns semigroup intertwining into the exact
Haar normalization of the kernel at every spatial pair.
-/

@[expose] public section

noncomputable section

open MeasureTheory

namespace HeatKernel

open RothschildStein

/-- Intertwining with normalized dilation gives the exact parabolic kernel scaling law. -/
theorem heatRepresentativeKernel_parabolic_scaling {n : ℕ} (G : HomogeneousGroup n)
    (T : ℝ → Lp ℝ 2 (volume : Measure (Fin n → ℝ)) →L[ℝ]
      Lp ℝ 2 (volume : Measure (Fin n → ℝ)))
    (u : ℝ → Lp ℝ 2 (volume : Measure (Fin n → ℝ)) → (Fin n → ℝ) → ℝ)
    (hu : ∀ t, 0 < t → ∀ f, Continuous (u t f))
    (hae : ∀ t, 0 < t → ∀ f, T t f =ᵐ[volume] u t f)
    {r t : ℝ} (hr : 0 < r) (ht : 0 < t)
    (hcomm : ∀ s, 0 < s → ∀ f,
      T s (dilationL2Equiv G hr f) = dilationL2Equiv G hr (T (r ^ 2 * s) f))
    (x y : Fin n → ℝ) :
    evaluationKernel (heatRepresentativeEvaluation T u hu hae) (r ^ 2 * t)
      (G.dilate r x) (G.dilate r y) = (r ^ G.homogeneousDimension)⁻¹ *
        evaluationKernel (heatRepresentativeEvaluation T u hu hae) t x y := by
  have hpull : ∀ f, (dilationL2Equiv G hr).symm.symm f =ᵐ[volume]
      fun z => Real.sqrt (r ^ G.homogeneousDimension) * f (G.dilate r z) := by
    simpa only [LinearIsometryEquiv.symm_symm] using ae_dilationL2Equiv_apply G hr
  have hc : Real.sqrt (r ^ G.homogeneousDimension) ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.mpr (pow_pos hr _))
  have hhalf : ∀ f, T (t / 2) ((dilationL2Equiv G hr).symm.symm f) =
      (dilationL2Equiv G hr).symm.symm (T (r ^ 2 * t / 2) f) := by
    intro f
    simpa only [LinearIsometryEquiv.symm_symm, mul_div_assoc] using hcomm (t / 2) (half_pos ht) f
  have h := heatRepresentativeKernel_covariance T u hu hae (dilationL2Equiv G hr).symm
    (G.dilate r) (G2.continuous_dilate G r) (quasiMeasurePreserving_group_dilate G hr)
    (Real.sqrt (r ^ G.homogeneousDimension)) hpull ht (mul_pos (sq_pos_of_pos hr) ht)
    hc hhalf x y
  simpa only [inv_pow, Real.sq_sqrt (pow_pos hr G.homogeneousDimension).le] using h

end HeatKernel
