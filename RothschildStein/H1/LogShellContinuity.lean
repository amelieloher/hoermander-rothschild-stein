-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H1.LogShellPrimitive
public import Mathlib.MeasureTheory.Integral.DominatedConvergence

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
open Set MeasureTheory Filter
open scoped Topology
namespace RothschildStein.H1
variable {N : ℕ} (G : HomogeneousGroup N)

/-- Continuity at the unit radius follows from shell
integrability and null gauge levels, by dominated convergence
(BB p. 274; explicit boundary-limit argument). -/
theorem continuousWithinAt_logShellPrimitive_zero
    {ν f : (Fin N → ℝ) → ℝ} (hν : G.IsHomogeneousGauge ν)
    (hf : ContinuousOn f {(0 : Fin N → ℝ)}ᶜ) :
    ContinuousWithinAt (logShellPrimitive ν f) (Ici 0) 0 := by
  let F (t : ℝ) := (gaugeShell ν 1 (Real.exp t)).indicator f
  let B := (gaugeShell ν 1 (Real.exp 1)).indicator (fun x => ‖f x‖)
  have hi (t : ℝ) : Integrable (F t) :=
    (integrable_indicator_iff (measurableSet_gaugeShell hν 1 (Real.exp t))).mpr
      (integrableOn_gaugeShell hν hf (by norm_num : (0 : ℝ) < 1))
  have hiB : Integrable B :=
    (integrable_indicator_iff (measurableSet_gaugeShell hν 1 (Real.exp 1))).mpr
      (integrableOn_gaugeShell hν hf (by norm_num : (0 : ℝ) < 1)).norm
  have hExp : Tendsto Real.exp (𝓝[≥] (0 : ℝ)) (𝓝 1) := by
    have he0 : Tendsto Real.exp (𝓝 (0 : ℝ)) (𝓝 (Real.exp 0)) :=
      Real.continuous_exp.continuousAt.tendsto
    have he1 : Tendsto Real.exp (𝓝 (0 : ℝ)) (𝓝 1) := by
      simpa only [Real.exp_zero] using he0
    exact he1.mono_left inf_le_left
  have hb : ∀ᶠ t : ℝ in 𝓝[≥] 0, ∀ᵐ x : Fin N → ℝ, ‖F t x‖ ≤ B x := by
    filter_upwards [(eventually_lt_nhds (by norm_num : (0 : ℝ) < 1)).filter_mono inf_le_left] with t ht
    apply Eventually.of_forall
    intro x
    by_cases hx : x ∈ gaugeShell ν 1 (Real.exp t)
    · have hxB : x ∈ gaugeShell ν 1 (Real.exp 1) :=
        ⟨hx.1, hx.2.trans (Real.exp_le_exp.mpr ht.le)⟩
      simp only [F, B, indicator_of_mem hx, indicator_of_mem hxB, le_refl]
    · rw [show F t x = 0 from indicator_of_notMem hx f]
      rw [norm_zero]
      change 0 ≤ (gaugeShell ν 1 (Real.exp 1)).indicator (fun y => ‖f y‖) x
      exact Set.indicator_nonneg (fun _ _ => norm_nonneg _) x
  have hl : ∀ᵐ x : Fin N → ℝ, Tendsto (fun t : ℝ => F t x) (𝓝[≥] 0) (𝓝 0) := by
    filter_upwards [ae_gauge_ne G hν (by norm_num : (0 : ℝ) < 1)] with x hx
    rcases lt_or_gt_of_ne hx with hx | hx
    · have he : (fun t : ℝ => F t x) = (fun _ => (0 : ℝ)) := by
        funext t
        exact indicator_of_notMem (fun h => (not_le.mpr hx) h.1) f
      rw [he]
      exact tendsto_const_nhds
    · apply tendsto_const_nhds.congr'
      filter_upwards [hExp.eventually (gt_mem_nhds hx)] with t ht
      exact (indicator_of_notMem (fun h => (not_le.mpr ht) h.2) f).symm
  have ht := tendsto_integral_filter_of_dominated_convergence B
    (Eventually.of_forall (fun t => (hi t).aestronglyMeasurable)) hb hiB hl
  have he (t : ℝ) : (∫ x, F t x) = logShellPrimitive ν f t :=
    integral_indicator (measurableSet_gaugeShell hν 1 (Real.exp t))
  change Tendsto (logShellPrimitive ν f) (𝓝[≥] 0) (𝓝 (logShellPrimitive ν f 0))
  rw [logShellPrimitive_zero G hν]
  simpa only [he, integral_zero] using ht

end RothschildStein.H1
