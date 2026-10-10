-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import Mathlib.Analysis.Calculus.Deriv.Slope
public import Mathlib.Analysis.Calculus.Deriv.Comp
public import Mathlib.Analysis.Normed.Operator.BoundedLinearMaps
public import Mathlib.Tactic.Module

/-! # Differentiation of a semigroup on a generator vector

The right quotient follows by applying a fixed operator. For the left quotient, the
semigroup law expresses the increment using a positive time step and an operator that
converges in norm.
-/

@[expose] public section
noncomputable section
open Set Filter
open scoped Topology
namespace HeatKernel
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem hasDerivAt_shift_sub {f : ℝ → E} {v : E} (s t : ℝ)
    (hf : HasDerivAt f v (t - s)) : HasDerivAt (fun r => f (r - s)) v t := by
  have hlin : HasDerivAt (fun r : ℝ => r - s) 1 t := by
    simpa only [id_eq] using (hasDerivAt_id t).sub_const s
  simpa only [one_smul, Function.comp_def] using hf.scomp t hlin

theorem hasDerivAt_semigroup_apply_of_generator_limit
    (T : ℝ → E →L[ℝ] E)
    (hadd : ∀ s t : ℝ, 0 ≤ s → 0 ≤ t → T (s + t) = T s * T t)
    (u v : E) (hgen : Tendsto (fun h : ℝ => h⁻¹ • (T h u - u)) (𝓝[>] 0) (𝓝 v))
    {t : ℝ} (ht : 0 < t) (hcont : ContinuousAt T t) :
    HasDerivAt (fun s => T s u) (T t v) t := by
  rw [hasDerivAt_iff_tendsto_slope_zero, ← nhdsLT_sup_nhdsGT, tendsto_sup]
  constructor
  · have hneg : Tendsto (fun h : ℝ => -h) (𝓝[<] 0) (𝓝[>] 0) := by
      apply tendsto_nhdsWithin_iff.mpr
      refine ⟨by simpa using (continuous_neg.tendsto (0 : ℝ)).mono_left nhdsWithin_le_nhds, ?_⟩
      filter_upwards [self_mem_nhdsWithin] with h hh
      exact neg_pos.mpr hh
    have hT : Tendsto (fun h : ℝ => T (t + h)) (𝓝[<] 0) (𝓝 (T t)) := by
      have hs : Tendsto (fun h : ℝ => t + h) (𝓝[<] 0) (𝓝 t) := by
        have hs' : Tendsto (fun h : ℝ => t + h) (𝓝[<] 0) (𝓝 (t + 0)) :=
          tendsto_const_nhds.add (tendsto_id.mono_left nhdsWithin_le_nhds)
        simpa only [add_zero] using hs'
      exact hcont.tendsto.comp hs
    have hev : Continuous (fun p : (E →L[ℝ] E) × E => p.1 p.2) :=
      continuous_fst.clm_apply continuous_snd
    have hl := (hev.tendsto (T t, v)).comp (hT.prodMk_nhds (hgen.comp hneg))
    apply hl.congr'
    have hsmall : ∀ᶠ h : ℝ in 𝓝[<] 0, -t < h :=
      Filter.Eventually.filter_mono nhdsWithin_le_nhds
        (lt_mem_nhds (show -t < (0 : ℝ) by linarith))
    filter_upwards [self_mem_nhdsWithin, hsmall] with h hh hht
    have htp : 0 ≤ t + h := by linarith
    have hhp : 0 ≤ -h := neg_nonneg.mpr (le_of_lt (show h < 0 from hh))
    have he : (t + h) + -h = t := by ring
    change T (t + h) ((-h)⁻¹ • (T (-h) u - u)) = h⁻¹ • (T (t + h) u - T t u)
    rw [map_smul, map_sub, ← mul_apply_eq_comp, ← hadd (t + h) (-h) htp hhp, he, inv_neg]
    module
  · have hr := (T t).continuous.tendsto v |>.comp hgen
    apply hr.congr'
    filter_upwards [self_mem_nhdsWithin] with h hh
    change T t (h⁻¹ • (T h u - u)) = h⁻¹ • (T (t + h) u - T t u)
    rw [hadd t h ht.le hh.le, mul_apply_eq_comp, map_smul, map_sub]

end HeatKernel
