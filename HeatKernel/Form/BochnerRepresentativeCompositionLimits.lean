-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Form.ContinuousBochnerComposition
import Mathlib.Tactic.Linter

/-! # Nonlinear Bochner limits for literal function representatives -/

@[expose] public section

noncomputable section

open MeasureTheory Filter TopologicalSpace
open scoped NNReal ENNReal Topology

namespace HeatKernel

/-- On a finite measure space, a continuous map with linear growth preserves L² convergence
of literal Bochner representatives along any filter. -/
theorem tendsto_eLpNorm_continuous_comp {A T E F : Type*} [MeasurableSpace T]
    {μ : Measure T} [IsFiniteMeasure μ]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
    {P : E → F} (hP : Continuous P) {C : ℝ≥0} (hb : ∀ u, ‖P u‖ ≤ (C : ℝ) * ‖u‖)
    {l : Filter A} {f : A → T → E} {g : T → E}
    (hf : ∀ a, MemLp (f a) 2 μ) (hg : MemLp g 2 μ)
    (hfg : Tendsto (fun a => eLpNorm (f a - g) 2 μ) l (𝓝 0)) :
    Tendsto (fun a => eLpNorm (fun t => P (f a t) - P (g t)) 2 μ) l (𝓝 0) := by
  let v : A → Lp E 2 μ := fun a => (hf a).toLp (f a)
  let u : Lp E 2 μ := hg.toLp g
  have hv : Tendsto v l (𝓝 u) := (Lp.tendsto_Lp_iff_tendsto_eLpNorm'' f hf g hg).mpr hfg
  have hc := (continuous_continuousBochnerComposition μ hP hb).continuousAt.tendsto.comp hv
  have hh := (Lp.tendsto_Lp_iff_tendsto_eLpNorm' _ _).mp hc
  apply hh.congr
  intro a
  apply eLpNorm_congr_ae
  filter_upwards [continuousBochnerComposition_coeFn_ae μ hP hb (v a),
    continuousBochnerComposition_coeFn_ae μ hP hb u, (hf a).coeFn_toLp, hg.coeFn_toLp]
    with t hfa hgu hft hgt
  change continuousBochnerComposition μ hP hb (v a) t - continuousBochnerComposition μ hP hb u t = _
  rw [hfa, hgu]
  change P ((hf a).toLp (f a) t) - P (hg.toLp g t) = _
  rw [hft, hgt]

/-- Eventual L² membership suffices for a continuous map with linear growth to preserve an
L² limit on a finite measure space. -/
theorem tendsto_eLpNorm_continuous_comp_of_eventually_memLp {A T E F : Type*} [MeasurableSpace T]
    {μ : Measure T} [IsFiniteMeasure μ]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
    {P : E → F} (hP : Continuous P) {C : ℝ≥0} (hb : ∀ u, ‖P u‖ ≤ (C : ℝ) * ‖u‖)
    {l : Filter A} {f : A → T → E} {g : T → E}
    (hf : ∀ᶠ a in l, MemLp (f a) 2 μ) (hg : MemLp g 2 μ)
    (hfg : Tendsto (fun a => eLpNorm (f a - g) 2 μ) l (𝓝 0)) :
    Tendsto (fun a => eLpNorm (fun t => P (f a t) - P (g t)) 2 μ) l (𝓝 0) := by
  classical
  let f' : A → T → E := fun a => if MemLp (f a) 2 μ then f a else g
  have hm : ∀ a, MemLp (f' a) 2 μ := by
    intro a
    by_cases ha : MemLp (f a) 2 μ
    · simpa only [f', ite_eq_left ha] using ha
    · simpa only [f', ite_eq_right ha] using hg
  have he : f' =ᶠ[l] f := hf.mono fun a ha => by simp only [f', ite_eq_left ha]
  have ht : Tendsto (fun a => eLpNorm (f' a - g) 2 μ) l (𝓝 0) :=
    (tendsto_congr' (he.mono fun a ha => congrArg (fun v => eLpNorm (v - g) 2 μ) ha)).mpr hfg
  apply (tendsto_eLpNorm_continuous_comp hP hb hm hg ht).congr'
  exact he.mono fun a ha => congrArg (fun v => eLpNorm (fun t => P (v t) - P (g t)) 2 μ) ha

end HeatKernel
