-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Moser.WeakSolutionAverageAdjoint
public import HeatKernel.Bridge.HilbertDualTimeAverages
public import HeatKernel.Form.TimeAverageIntegrability

/-! # Integrability of translated time pairings -/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
open MeasureTheory Set
namespace HeatKernel

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- An integrable curve paired with a bounded continuous time test has an
integrable backward translated pairing on any bounded averaging interval. -/
theorem integrable_backward_time_pair {F : ℝ → E} (hF : Integrable F)
    {ψ : ℝ → ℝ} (hψ : Continuous ψ) (hc : HasCompactSupport ψ) (h : ℝ) :
    Integrable (fun z : ℝ × ℝ => ψ (z.2 - z.1) • F z.2)
      ((volume.restrict (uIoc 0 h)).prod volume) := by
  let : IsFiniteMeasure (volume.restrict (uIoc 0 h)) :=
    isFiniteMeasure_restrict.mpr
      ((measure_mono uIoc_subset_uIcc).trans_lt isCompact_uIcc.measure_lt_top).ne
  obtain ⟨C, hC⟩ := hc.exists_bound_of_continuous hψ
  have hm : AEStronglyMeasurable
      (fun z : ℝ × ℝ => ψ (z.2 - z.1) • F z.2)
      ((volume.restrict (uIoc 0 h)).prod volume) :=
    (hψ.comp (continuous_snd.sub continuous_fst)).aestronglyMeasurable.smul
      hF.aestronglyMeasurable.comp_snd
  apply ((hF.norm.comp_snd (volume.restrict (uIoc 0 h))).const_mul C).mono' hm
  filter_upwards [] with z
  rw [norm_smul]
  exact mul_le_mul_of_nonneg_right (hC _) (norm_nonneg _)

/-- Translation shear transfers integrability to the forward pairing. -/
theorem integrable_forward_time_pair {F : ℝ → E} (hF : Integrable F)
    {ψ : ℝ → ℝ} (hψ : Continuous ψ) (hc : HasCompactSupport ψ) (h : ℝ) :
    Integrable (fun z : ℝ × ℝ => ψ z.2 • F (z.2 + z.1))
      ((volume.restrict (uIoc 0 h)).prod volume) := by
  have hi := (measurePreserving_prod_add_right
    (μ := volume.restrict (uIoc 0 h)) (ν := volume)).integrable_comp_of_integrable
      (integrable_backward_time_pair hF hψ hc h)
  simpa only [Function.comp_def, add_sub_cancel_right] using hi

/-- Compact smooth tests satisfy the adjoint average identity without any
additional product integrability hypotheses. -/
theorem integral_backwardTimeAverage_smul_eq_of_integrable [CompleteSpace E]
    {F : ℝ → E} (hF : Integrable F) {ψ : ℝ → ℝ}
    (hψ : Continuous ψ) (hc : HasCompactSupport ψ) (h : ℝ) :
    (∫ t, backwardTimeAverage h ψ t • F t) =
      ∫ t, ψ t • forwardTimeAverage h F t :=
  integral_backwardTimeAverage_smul_eq h
    (integrable_backward_time_pair hF hψ hc h)
    (integrable_forward_time_pair hF hψ hc h)

/-- Forward averaging preserves square integrability in the continuous dual
of a real Hilbert space, with its existing operator norm. -/
theorem memLp_forwardDualTimeAverage {V : Type*} [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] [CompleteSpace V] {F : ℝ → (V →L[ℝ] ℝ)}
    (hF : MemLp F 2 volume) {h : ℝ} (hh : 0 ≤ h) :
    MemLp (forwardTimeAverage h F) 2 volume := by
  let : InnerProductSpace ℝ (V →L[ℝ] ℝ) := hilbertDualInnerProductSpace V
  exact memLp_forwardTimeAverage hF hh

end HeatKernel
