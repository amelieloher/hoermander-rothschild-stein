-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.G2.MollifierBound
public import RothschildStein.G2.ConvolutionMeasurable
public import Mathlib.MeasureTheory.Integral.Lebesgue.DominatedConvergence
public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
public import Mathlib.Analysis.Normed.Group.Bounded

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
open MeasureTheory Filter Set
open scoped Topology ENNReal
namespace RothschildStein.G2
variable {N : ℕ} (G : HomogeneousGroup N) {ν : HomogeneousNorm G}

/-- Compact continuous inputs converge in every finite Lp
power integral (BB Prop 3.48 proof, p. 122; dominated convergence on the
proved common compact support). -/
theorem tendsto_groupRegularize_compact_power (φ : GroupMollifier G ν)
    {f : (Fin N → ℝ) → ℝ} (hf : Continuous f) (hcf : HasCompactSupport f)
    {p : ℝ} (hp : 0 < p) :
    Tendsto (fun ε : ℝ => ∫⁻ x, ‖groupRegularize G φ f ε x - f x‖ₑ ^ p)
      (𝓝[>] 0) (𝓝 0) := by
  obtain ⟨C, hC⟩ := hf.bounded_above_of_compact_support hcf
  obtain ⟨K, hK, hfK, hregK⟩ := exists_common_compact_support_groupRegularize G φ hcf
  let B : (Fin N → ℝ) → ℝ≥0∞ := K.indicator (fun _ => ENNReal.ofReal (2 * C) ^ p)
  have hm (ε : ℝ) : Measurable (fun x => ‖groupRegularize G φ f ε x - f x‖ₑ ^ p) :=
    ((stronglyMeasurable_groupConvolution G
      (contDiff_groupMollifierScale G φ ε).continuous.stronglyMeasurable
      hf.stronglyMeasurable).measurable.sub hf.measurable).enorm.pow_const p
  have hsmall : ∀ᶠ ε : ℝ in 𝓝[>] 0, 0 < ε ∧ ε ≤ 1 := by
    filter_upwards [Ioo_mem_nhdsGT zero_lt_one] with ε hε
    exact ⟨hε.1, hε.2.le⟩
  have hb : ∀ᶠ ε : ℝ in 𝓝[>] 0, ∀ᵐ x ∂volume,
      ‖groupRegularize G φ f ε x - f x‖ₑ ^ p ≤ B x := by
    filter_upwards [hsmall] with ε hε
    apply Eventually.of_forall
    intro x
    by_cases hx : x ∈ K
    · change _ ≤ K.indicator (fun _ => ENNReal.ofReal (2 * C) ^ p) x
      rw [indicator_of_mem hx]
      apply ENNReal.rpow_le_rpow _ hp.le
      rw [← ofReal_norm]
      apply ENNReal.ofReal_le_ofReal
      exact (norm_sub_le _ _).trans (by
        have H := norm_groupRegularize_le G φ hf hC hε.1 x
        linarith [hC x])
    · have hz : groupRegularize G φ f ε x = 0 := by
        by_contra hn
        exact hx (hregK ε hε.1 hε.2 hn)
      have hfx : f x = 0 := image_eq_zero_of_notMem_tsupport (fun hs => hx (hfK hs))
      simp only [B, indicator_of_notMem hx, hz, hfx, sub_self, enorm_zero,
        ENNReal.zero_rpow_of_pos hp, le_refl]
  have hfin : (∫⁻ x, B x) ≠ ⊤ := by
    rw [lintegral_indicator hK.measurableSet, lintegral_const, Measure.restrict_apply_univ]
    exact (ENNReal.mul_lt_top
      (ENNReal.rpow_lt_top_of_nonneg hp.le ENNReal.ofReal_ne_top) hK.measure_lt_top).ne
  have ht : ∀ᵐ x ∂volume, Tendsto (fun ε : ℝ => ‖groupRegularize G φ f ε x - f x‖ₑ ^ p)
      (𝓝[>] 0) (𝓝 (0 : ℝ≥0∞)) := by
    apply Eventually.of_forall
    intro x
    have H := ((tendsto_groupRegularize_pointwise G φ hf hC x).sub (tendsto_const_nhds (x := f x))).enorm
    have Hpow := H.ennrpow_const p
    simpa only [sub_self, enorm_zero, ENNReal.zero_rpow_of_pos hp] using Hpow
  have H := tendsto_lintegral_filter_of_dominated_convergence B
    (Eventually.of_forall hm) hb hfin ht
  simpa only [lintegral_zero] using H

/-- Compact continuous inputs converge in each finite Lp norm
(BB Prop 3.48 proof, p. 122). -/
theorem tendsto_groupRegularize_compact_eLpNorm (φ : GroupMollifier G ν)
    {f : (Fin N → ℝ) → ℝ} (hf : Continuous f) (hcf : HasCompactSupport f)
    {p : ℝ} (hp : 0 < p) :
    Tendsto (fun ε : ℝ => eLpNorm (groupRegularize G φ f ε - f) (ENNReal.ofReal p) volume)
      (𝓝[>] 0) (𝓝 0) := by
  have H := (tendsto_groupRegularize_compact_power G φ hf hcf hp).ennrpow_const (1 / p)
  have he (ε : ℝ) : eLpNorm (groupRegularize G φ f ε - f) (ENNReal.ofReal p) volume =
      (∫⁻ x, ‖groupRegularize G φ f ε x - f x‖ₑ ^ p) ^ (1 / p) := by
    have hm : AEStronglyMeasurable (groupRegularize G φ f ε - f) volume :=
      (aestronglyMeasurable_groupConvolution G
        (contDiff_groupMollifierScale G φ ε).continuous.aestronglyMeasurable
        hf.aestronglyMeasurable).sub hf.aestronglyMeasurable
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (ENNReal.ofReal_pos.mpr hp).ne'
      ENNReal.ofReal_ne_top hm, ENNReal.toReal_ofReal hp.le]
    rfl
  simpa only [← he, ENNReal.zero_rpow_of_pos (div_pos zero_lt_one hp)] using H

end RothschildStein.G2
