-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H1.SharpShellCutoffDilation
public import Mathlib.MeasureTheory.Integral.DominatedConvergence

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public section
noncomputable section
open Set Filter MeasureTheory
open scoped Topology
namespace RothschildStein.H1
variable {N : ℕ} (G : HomogeneousGroup N)

/-- Step 3: smooth cutoff differences converge under the
integral to the actual shell integral, with a fixed compact-shell
dominator (BB Corollary 6.31, p. 280). -/
theorem tendsto_integral_sharpShellCutoff_difference
    {ν f : (Fin N → ℝ) → ℝ} (hν : G.IsHomogeneousGauge ν)
    (hf : ContinuousOn f {(0 : Fin N → ℝ)}ᶜ)
    {η : ℕ → (Fin N → ℝ) → ℝ} (hc : ∀ n, Continuous (η n))
    (hb : ∀ n x, 0 ≤ η n x ∧ η n x ≤ 1)
    (hi : ∀ n x, ν x ≤ 1 - (1 / 2 : ℝ) ^ (n + 1) → η n x = 1)
    (ho : ∀ n x, 1 ≤ ν x → η n x = 0)
    {r R : ℝ} (hr : 0 < r) (hrR : r < R) :
    Tendsto (fun n => ∫ x, f x * (η n (G.dilate R⁻¹ x) - η n (G.dilate r⁻¹ x)))
      atTop (𝓝 (∫ x in gaugeShell ν r R, f x)) := by
  let S := gaugeShell ν (r / 2) R
  let F (n : ℕ) (x : Fin N → ℝ) :=
    f x * (η n (G.dilate R⁻¹ x) - η n (G.dilate r⁻¹ x))
  let B := S.indicator (fun x => ‖f x‖)
  have hS := measurableSet_gaugeShell hν (r / 2) R
  have hB : Integrable B := (integrable_indicator_iff hS).mpr
    (integrableOn_gaugeShell hν hf (half_pos hr)).norm
  have hbF (n : ℕ) (x : Fin N → ℝ) : ‖F n x‖ ≤ B x := by
    have hd := sharpShellCutoff_difference_bound G hν hb hi ho hr hrR n x
    change ‖f x * (η n (G.dilate R⁻¹ x) - η n (G.dilate r⁻¹ x))‖ ≤ S.indicator (fun x => ‖f x‖) x
    rw [norm_mul]
    by_cases hx : x ∈ S
    · rw [indicator_of_mem hx] at hd ⊢
      exact (mul_le_mul_of_nonneg_left hd (norm_nonneg _)).trans_eq (mul_one _)
    · rw [indicator_of_notMem hx] at hd ⊢
      exact (mul_le_mul_of_nonneg_left hd (norm_nonneg _)).trans_eq (mul_zero _)
  have hIF (n : ℕ) : Integrable (F n) := by
    have hCF : ContinuousOn (F n) S :=
      (hf.mono (gaugeShell_subset_punctured hν (half_pos hr))).mul
        (((hc n).comp (G2.continuous_dilate G R⁻¹)).sub
          ((hc n).comp (G2.continuous_dilate G r⁻¹))).continuousOn
    have hiF : Integrable (S.indicator (F n)) := (integrable_indicator_iff hS).mpr
      (hCF.integrableOn_compact (isCompact_gaugeShell hν _ _))
    apply hiF.congr
    apply Eventually.of_forall
    intro x
    by_cases hx : x ∈ S
    · exact indicator_of_mem hx (F n)
    · rw [indicator_of_notMem hx]
      have hz := hbF n x
      change ‖F n x‖ ≤ S.indicator (fun x => ‖f x‖) x at hz
      rw [indicator_of_notMem hx] at hz
      exact (norm_eq_zero.mp (le_antisymm hz (norm_nonneg _))).symm
  have hl : ∀ᵐ x : Fin N → ℝ,
      Tendsto (fun n => F n x) atTop (𝓝 ((gaugeShell ν r R).indicator f x)) := by
    filter_upwards [ae_gauge_ne G hν (hr.trans hrR)] with x hxR
    have ht := (tendsto_const_nhds : Tendsto (fun _ : ℕ => f x) atTop (𝓝 (f x))).mul
      ((tendsto_sharpShellCutoff_dilate G hν hi ho (hr.trans hrR) x).sub
        (tendsto_sharpShellCutoff_dilate G hν hi ho hr x))
    by_cases hxr : ν x < r
    · have hxR' : ν x < R := hxr.trans hrR
      have hxS : x ∉ gaugeShell ν r R := fun h => (not_le.mpr hxr) h.1
      simpa only [ite_eq_left hxr, ite_eq_left hxR', sub_self, mul_zero,
        indicator_of_notMem hxS] using ht
    · by_cases hxR' : ν x < R
      · have hxS : x ∈ gaugeShell ν r R := ⟨le_of_not_gt hxr, hxR'.le⟩
        simpa only [ite_eq_right hxr, ite_eq_left hxR', sub_zero, mul_one,
          indicator_of_mem hxS] using ht
      · have hxS : x ∉ gaugeShell ν r R := by
          intro h
          exact hxR (le_antisymm h.2 (le_of_not_gt hxR'))
        simpa only [ite_eq_right hxr, ite_eq_right hxR', sub_self, mul_zero,
          indicator_of_notMem hxS] using ht
  have ht := tendsto_integral_filter_of_dominated_convergence B
    (Eventually.of_forall fun n => (hIF n).aestronglyMeasurable)
    (Eventually.of_forall fun n => Eventually.of_forall (hbF n)) hB hl
  rw [integral_indicator (measurableSet_gaugeShell hν r R)] at ht
  exact ht

end RothschildStein.H1
