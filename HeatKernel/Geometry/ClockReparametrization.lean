-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Geometry.IntegralClock
public import HeatKernel.Geometry.CurveReparametrization
public import Mathlib.Analysis.Calculus.Deriv.Inverse
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.LebesgueDifferentiationThm

/-! Absolute continuity and differentiation under inverse integral clocks. -/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set MeasureTheory Filter
open scoped Topology NNReal
namespace HeatKernel

/-- The inverse of an integral clock is nonsingular for the restricted interval measures. -/
theorem quasiMeasurePreserving_inverse_clock {e : ℝ ≃o ℝ} {w : ℝ → ℝ}
    (hw : IntegrableOn w (Icc 0 1))
    (hn : ∀ᵐ u ∂volume.restrict (Icc (0 : ℝ) 1), 0 ≤ w u)
    (he : ∀ t ∈ Icc (0 : ℝ) 1, e t = ∫ u in Icc (0 : ℝ) t, w u) :
    Measure.QuasiMeasurePreserving e.symm (volume.restrict (Icc (e 0) (e 1)))
      (volume.restrict (Icc (0 : ℝ) 1)) := by
  refine ⟨e.symm.continuous.measurable, ?_⟩
  rw [map_inverse_clock_eq_withDensity e w hw hn he]
  exact withDensity_absolutelyContinuous _ _

/-- A curve remains absolutely continuous under a Lipschitz inverse clock. -/
theorem absolutelyContinuousOnInterval_comp_inverse_clock {E : Type*} [PseudoMetricSpace E]
    {γ : ℝ → E} {e : ℝ ≃o ℝ} {K : ℝ≥0}
    (hγ : AbsolutelyContinuousOnInterval γ 0 1) (hK : LipschitzWith K e.symm) :
    AbsolutelyContinuousOnInterval (γ ∘ e.symm) (e 0) (e 1) := by
  apply absolutelyContinuousOnInterval_comp_of_monotone hγ (Or.inl e.symm.monotone)
    hK.lipschitzOnWith
  intro u hu
  have h01 : (0 : ℝ) ≤ 1 := by norm_num
  simp only [uIcc_of_le (e.monotone h01), mem_Icc] at hu
  simp only [uIcc_of_le h01, mem_Icc]
  constructor
  · simpa only [e.symm_apply_apply] using e.symm.monotone hu.1
  · simpa only [e.symm_apply_apply] using e.symm.monotone hu.2

/-- An integral clock has its prescribed derivative almost everywhere on the unit interval. -/
theorem ae_hasDerivAt_integral_clock {e : ℝ ≃o ℝ} {w : ℝ → ℝ}
    (hw : IntegrableOn w (Icc 0 1))
    (he : ∀ t ∈ Icc (0 : ℝ) 1, e t = ∫ u in Icc (0 : ℝ) t, w u) :
    ∀ᵐ u ∂volume.restrict (Icc (0 : ℝ) 1), HasDerivAt e (w u) u := by
  have hi : IntervalIntegrable w volume 0 1 :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le (by norm_num : (0 : ℝ) ≤ 1)).2 hw
  filter_upwards [ae_restrict_of_ae hi.ae_hasDerivAt_integral,
    ae_restrict_mem measurableSet_Icc, (volume.restrict (Icc (0 : ℝ) 1)).ae_ne 0,
    (volume.restrict (Icc (0 : ℝ) 1)).ae_ne 1] with u hu humem hu0 hu1
  have hderiv := hu (by simpa only [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using humem)
    0 (by simp)
  apply hderiv.congr_of_eventuallyEq
  filter_upwards [Ioo_mem_nhds (lt_of_le_of_ne humem.1 (Ne.symm hu0))
    (lt_of_le_of_ne humem.2 hu1)] with v hv
  change e v = ∫ z in (0 : ℝ)..v, w z
  rw [he v ⟨hv.1.le, hv.2.le⟩, integral_Icc_eq_integral_Ioc,
    intervalIntegral.integral_of_le hv.1.le]

/-- The derivative of the inverse clock is the reciprocal of the transported density. -/
theorem ae_hasDerivAt_inverse_clock {e : ℝ ≃o ℝ} {w : ℝ → ℝ}
    (hw : IntegrableOn w (Icc 0 1))
    (hp : ∀ᵐ u ∂volume.restrict (Icc (0 : ℝ) 1), 0 < w u)
    (he : ∀ t ∈ Icc (0 : ℝ) 1, e t = ∫ u in Icc (0 : ℝ) t, w u) :
    ∀ᵐ u ∂volume.restrict (Icc (e 0) (e 1)), HasDerivAt e.symm (w (e.symm u))⁻¹ u := by
  have hq := quasiMeasurePreserving_inverse_clock hw (hp.mono fun _ hu => hu.le) he
  filter_upwards [hq.ae (ae_hasDerivAt_integral_clock hw he), hq.ae hp] with u hu hpos
  exact HasDerivAt.of_local_left_inverse e.symm.continuous.continuousAt hu hpos.ne'
    (Eventually.of_forall e.apply_symm_apply)

end HeatKernel
