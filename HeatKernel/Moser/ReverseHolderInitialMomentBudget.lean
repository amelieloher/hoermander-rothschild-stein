-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Moser.ReverseHolderInitialTimes
public import HeatKernel.Moser.ReverseHolderTimeWeightedBudget
public import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Tactic

/-! Uniform backward time-energy budgets from literal value moments -/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set MeasureTheory Filter
open scoped Topology
namespace HeatKernel

/-- A common time representative transfers all lower-endpoint budgets to the
literal energy almost everywhere. -/
theorem ae_initial_energy_budgets_of_representative
    {a b : ℝ} {e E D R χ : ℝ → ℝ}
    (heq : e =ᵐ[volume.restrict (Icc a b)] E)
    (hE : IntegrableOn E (Icc a b)) (hR : IntegrableOn R (Icc a b))
    (hχ : ContDiff ℝ 1 χ)
    (hbudget : ∀ s ∈ Icc a b,
      χ s * e s + (∫ t in s..b, χ t * D t) ≤
        (∫ t in s..b, -(deriv χ t) * e t) + ∫ t in s..b, χ t * R t) :
    ∀ᵐ s ∂volume.restrict (Icc a b),
      χ s * E s + (∫ t in Icc s b, χ t * D t) ≤
        ∫ t in Icc s b, -(deriv χ t) * E t + χ t * R t := by
  have hχE : IntegrableOn (fun t => -(deriv χ t) * E t) (Icc a b) :=
    IntegrableOn.continuousOn_mul hχ.continuous_deriv_one.neg.continuousOn hE isCompact_Icc
  have hχR : IntegrableOn (fun t => χ t * R t) (Icc a b) :=
    IntegrableOn.continuousOn_mul hχ.continuous.continuousOn hR isCompact_Icc
  filter_upwards [heq, self_mem_ae_restrict measurableSet_Icc] with s hs hsm
  have hsub : Icc s b ⊆ Icc a b := Icc_subset_Icc_left hsm.1
  have hi : (∫ t in Icc s b, -(deriv χ t) * e t) =
      ∫ t in Icc s b, -(deriv χ t) * E t := by
    apply integral_congr_ae
    filter_upwards [heq.filter_mono (ae_mono (Measure.restrict_mono hsub le_rfl))] with t ht
    rw [ht]
  have hb := hbudget s hsm
  simp only [intervalIntegral.integral_of_le hsm.2, ← integral_Icc_eq_integral_Ioc] at hb
  rw [hs, hi] at hb
  simpa only [integral_add (hχE.mono_set hsub) (hχR.mono_set hsub)] using hb

/-- A unit cutoff vanishing at the top gives uniform lower-endpoint and
integrated dissipation bounds from the full literal value moment. The energy
budget and the comparison with that moment are explicit inputs. -/
theorem initial_energy_budget_le_full_value_moment
    {a b H L : ℝ} (hab : a < b) (hH : 0 ≤ H) (hL : 0 ≤ L)
    {E D R m χ : ℝ → ℝ}
    (hE : IntegrableOn E (Icc a b)) (hD : IntegrableOn D (Icc a b))
    (hR : IntegrableOn R (Icc a b)) (hm : IntegrableOn m (Icc a b))
    (hRbound : ∀ᵐ t ∂volume.restrict (Icc a b), R t ≤ 2 * L * m t)
    (hm0 : ∀ᵐ t ∂volume.restrict (Icc a b), 0 ≤ m t)
    (hD0 : ∀ᵐ t ∂volume.restrict (Icc a b), 0 ≤ D t)
    (hE0 : ∀ᵐ t ∂volume.restrict (Icc a b), 0 ≤ E t)
    (hEm : ∀ᵐ t ∂volume.restrict (Icc a b), E t ≤ m t)
    (hχ : ContDiff ℝ 1 χ)
    (hχunit : ∀ t ∈ Icc a b, χ t ∈ Icc (0 : ℝ) 1)
    (hχderiv : ∀ t ∈ Icc a b, -(deriv χ t) ≤ H)
    (hbudget : ∀ᵐ s ∂volume.restrict (Icc a b),
      χ s * E s + (∫ t in Icc s b, χ t * D t) ≤
        ∫ t in Icc s b, -(deriv χ t) * E t + χ t * R t) :
    (∀ᵐ s ∂volume.restrict (Icc a b),
      χ s * E s ≤ (H + 2 * L) * (∫ t in Icc a b, m t)) ∧
      (∫ t in Icc a b, χ t * D t) ≤
        (H + 2 * L) * (∫ t in Icc a b, m t) := by
  have hC : 0 ≤ H + 2 * L := by positivity
  have hχE : IntegrableOn (fun t => -(deriv χ t) * E t) (Icc a b) :=
    IntegrableOn.continuousOn_mul hχ.continuous_deriv_one.neg.continuousOn hE isCompact_Icc
  have hχR : IntegrableOn (fun t => χ t * R t) (Icc a b) :=
    IntegrableOn.continuousOn_mul hχ.continuous.continuousOn hR isCompact_Icc
  have hχD : IntegrableOn (fun t => χ t * D t) (Icc a b) :=
    IntegrableOn.continuousOn_mul hχ.continuous.continuousOn hD isCompact_Icc
  have hCm : IntegrableOn (fun t => (H + 2 * L) * m t) (Icc a b) :=
    hm.const_mul (H + 2 * L)
  have hpoint : ∀ᵐ t ∂volume.restrict (Icc a b),
      -(deriv χ t) * E t + χ t * R t ≤ (H + 2 * L) * m t := by
    filter_upwards [hm0, hE0, hEm, hRbound, self_mem_ae_restrict measurableSet_Icc]
      with t hmz he0 hem hr ht
    have h1 := mul_le_mul_of_nonneg_right (hχderiv t ht) he0
    have h2 := mul_le_mul_of_nonneg_left hem hH
    have h3 := mul_le_mul_of_nonneg_right (hχunit t ht).2
      (show 0 ≤ 2 * L * m t by positivity)
    have h4 := mul_le_mul_of_nonneg_left hr (hχunit t ht).1
    nlinarith only [h1, h2, h3, h4]
  have hb : ∀ᵐ s ∂volume.restrict (Icc a b),
      χ s * E s + (∫ t in Icc s b, χ t * D t) ≤
        (H + 2 * L) * (∫ t in Icc a b, m t) := by
    filter_upwards [hbudget, self_mem_ae_restrict measurableSet_Icc] with s hs hsm
    have hsub : Icc s b ⊆ Icc a b := Icc_subset_Icc_left hsm.1
    have hi := integral_mono_ae ((hχE.add hχR).mono_set hsub)
      (hCm.mono_set hsub)
      (hpoint.filter_mono (ae_mono (Measure.restrict_mono hsub le_rfl)))
    simp only [Pi.add_apply] at hi
    rw [integral_const_mul] at hi
    have hmle := setIntegral_mono_set hm hm0 (Filter.Eventually.of_forall hsub)
    exact hs.trans (hi.trans (mul_le_mul_of_nonneg_left hmle hC))
  have hsup : ∀ᵐ s ∂volume.restrict (Icc a b),
      χ s * E s ≤ (H + 2 * L) * (∫ t in Icc a b, m t) := by
    filter_upwards [hb, self_mem_ae_restrict measurableSet_Icc] with s hs hsm
    have hnonneg : 0 ≤ ∫ t in Icc s b, χ t * D t := by
      apply integral_nonneg_of_ae
      filter_upwards [(hD0.and (self_mem_ae_restrict measurableSet_Icc)).filter_mono
        (ae_mono (Measure.restrict_mono (Icc_subset_Icc_left hsm.1) le_rfl))] with t ht
      exact mul_nonneg (hχunit t ht.2).1 ht.1
    linarith
  refine ⟨hsup, ?_⟩
  have hacc : ∀ᵐ s ∂volume.restrict (Icc a b),
      (∫ t in Icc s b, χ t * D t) ≤ (H + 2 * L) * (∫ t in Icc a b, m t) := by
    filter_upwards [hb, hE0, self_mem_ae_restrict measurableSet_Icc] with s hs he0 hsm
    have hpos := mul_nonneg (hχunit s hsm).1 he0
    linarith
  have hacc' := hacc.filter_mono
    (ae_mono (Measure.restrict_mono Ioo_subset_Icc_self le_rfl))
  obtain ⟨s, hmono, hs, ht⟩ := exists_strictAnti_good_initial_times hab hacc'
  have hlim := tendsto_integral_Icc_of_decreasing_initial_times a b s hmono.antitone
    (fun n => ⟨(hs n).1, (hs n).2.1⟩) ht (fun t => χ t * D t)
      (hχD.mono_set Ioc_subset_Icc_self)
  have htotal := le_of_tendsto hlim (Filter.Eventually.of_forall fun n => (hs n).2.2)
  simpa only [integral_Icc_eq_integral_Ioc] using htotal

end HeatKernel
