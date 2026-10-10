-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Moser.TopExhaustionEnergyTrace
public import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Tactic

/-! # Uniform time-energy budgets from a quadratic value moment -/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set MeasureTheory Filter
open scoped Topology
namespace HeatKernel

/-- A terminal energy inequality with a unit temporal cutoff is bounded by the
full value moment. The same constant controls the dissipation at the upper time,
using good terminal times and integrability. The energy inequality and the
comparison between primitive and value energy are explicit inputs. -/
theorem terminal_energy_budget_le_full_value_moment
    {a b p H L : ℝ} (hab : a < b) (hp : 0 < p) (hH : 0 ≤ H) (hL : 0 ≤ L)
    {E D m χ : ℝ → ℝ}
    (hE : IntegrableOn E (Icc a b)) (hD : IntegrableOn D (Icc a b))
    (hm : IntegrableOn m (Icc a b))
    (hm0 : ∀ᵐ t ∂volume.restrict (Icc a b), 0 ≤ m t)
    (hE0 : ∀ᵐ t ∂volume.restrict (Icc a b), 0 ≤ E t)
    (hEm : ∀ᵐ t ∂volume.restrict (Icc a b), E t ≤ m t / p)
    (hχ : ContDiff ℝ 1 χ)
    (hχunit : ∀ t ∈ Icc a b, χ t ∈ Icc (0 : ℝ) 1)
    (hχderiv : ∀ t ∈ Icc a b, deriv χ t ≤ H)
    (hbudget : ∀ᵐ s ∂volume.restrict (Icc a b),
      χ s * E s + (∫ t in Icc a s, χ t * D t) ≤
        ∫ t in Icc a s, deriv χ t * E t + χ t * (2 * L * m t)) :
    (∀ᵐ s ∂volume.restrict (Icc a b),
      χ s * E s + (∫ t in Icc a s, χ t * D t) ≤
        (H / p + 2 * L) * (∫ t in Icc a b, m t)) ∧
      (∫ t in Icc a b, χ t * D t) ≤
        (H / p + 2 * L) * (∫ t in Icc a b, m t) := by
  have hC : 0 ≤ H / p + 2 * L := by positivity
  have hχE : IntegrableOn (fun t => deriv χ t * E t) (Icc a b) :=
    IntegrableOn.continuousOn_mul hχ.continuous_deriv_one.continuousOn hE isCompact_Icc
  have hχm : IntegrableOn (fun t => χ t * (2 * L * m t)) (Icc a b) :=
    IntegrableOn.continuousOn_mul hχ.continuous.continuousOn (hm.const_mul (2 * L)) isCompact_Icc
  have hχD : IntegrableOn (fun t => χ t * D t) (Icc a b) :=
    IntegrableOn.continuousOn_mul hχ.continuous.continuousOn hD isCompact_Icc
  have hCm : IntegrableOn (fun t => (H / p + 2 * L) * m t) (Icc a b) :=
    hm.const_mul (H / p + 2 * L)
  have hpoint : ∀ᵐ t ∂volume.restrict (Icc a b),
      deriv χ t * E t + χ t * (2 * L * m t) ≤ (H / p + 2 * L) * m t := by
    filter_upwards [hm0, hE0, hEm, self_mem_ae_restrict measurableSet_Icc] with t hmz he0 hem ht
    have h1 := mul_le_mul_of_nonneg_right (hχderiv t ht) he0
    have h2 := mul_le_mul_of_nonneg_left hem hH
    have h3 := mul_le_mul_of_nonneg_right (hχunit t ht).2
      (show 0 ≤ 2 * L * m t by positivity)
    have heq : H * (m t / p) = (H / p) * m t := by ring
    rw [heq] at h2
    nlinarith only [h1, h2, h3]
  have hb : ∀ᵐ s ∂volume.restrict (Icc a b),
      χ s * E s + (∫ t in Icc a s, χ t * D t) ≤
        (H / p + 2 * L) * (∫ t in Icc a b, m t) := by
    filter_upwards [hbudget, self_mem_ae_restrict measurableSet_Icc] with s hs hsm
    have hsub : Icc a s ⊆ Icc a b := Icc_subset_Icc_right hsm.2
    have hi := integral_mono_ae ((hχE.add hχm).mono_set hsub)
      (hCm.mono_set hsub)
      (hpoint.filter_mono (ae_mono (Measure.restrict_mono hsub le_rfl)))
    simp only [Pi.add_apply] at hi
    rw [integral_const_mul] at hi
    have hmle := setIntegral_mono_set hm hm0 (Filter.Eventually.of_forall hsub)
    exact hs.trans (hi.trans (mul_le_mul_of_nonneg_left hmle hC))
  refine ⟨hb, ?_⟩
  have hacc : ∀ᵐ s ∂volume.restrict (Icc a b),
      (∫ t in Icc a s, χ t * D t) ≤ (H / p + 2 * L) * (∫ t in Icc a b, m t) := by
    filter_upwards [hb, hE0, self_mem_ae_restrict measurableSet_Icc] with s hs he0 hsm
    have hpos := mul_nonneg (hχunit s hsm).1 he0
    linarith
  have hacc' := hacc.filter_mono
    (ae_mono (Measure.restrict_mono Ioo_subset_Icc_self le_rfl))
  obtain ⟨s, hmono, hs, ht⟩ := exists_strictMono_good_terminal_times hab hacc'
  have hlim := tendsto_integral_Icc_of_cofinal_times a b s hmono.monotone
    (fun n => ⟨(hs n).1, (hs n).2.1⟩) ht (fun t => χ t * D t)
      (hχD.mono_set Ico_subset_Icc_self)
  have htotal := le_of_tendsto hlim (Filter.Eventually.of_forall fun n => (hs n).2.2)
  simpa only [integral_Icc_eq_integral_Ico] using htotal

end HeatKernel
