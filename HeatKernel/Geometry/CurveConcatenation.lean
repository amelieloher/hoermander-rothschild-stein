-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Geometry.AffineReparametrization

/-! Concatenation of absolutely continuous horizontal curves. -/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set MeasureTheory
open scoped BigOperators NNReal Topology
namespace HeatKernel

/-- Two absolutely continuous curves agreeing at a common endpoint concatenate to
an absolutely continuous curve. -/
theorem absolutelyContinuousOnInterval_piecewise {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] {f g : ℝ → E} {s c t : ℝ}
    (hsc : s ≤ c) (hct : c ≤ t) (hf : AbsolutelyContinuousOnInterval f s c)
    (hg : AbsolutelyContinuousOnInterval g c t) (he : f c = g c) :
    AbsolutelyContinuousOnInterval (fun u => if u ≤ c then f u else g u) s t := by
  have hl : AbsolutelyContinuousOnInterval (fun u => f (min u c)) s t :=
    absolutelyContinuousOnInterval_comp_of_monotone hf
      (Or.inl (by intro u v huv; exact min_le_min_right c huv))
      (LipschitzWith.id.min_const c).lipschitzOnWith (by
        intro u hu
        simp only [uIcc_of_le (hsc.trans hct), mem_Icc] at hu
        simp only [uIcc_of_le hsc, mem_Icc]
        exact ⟨le_min hu.1 hsc, min_le_right _ _⟩)
  have hr : AbsolutelyContinuousOnInterval (fun u => g (max u c)) s t :=
    absolutelyContinuousOnInterval_comp_of_monotone hg
      (Or.inl (by intro u v huv; exact max_le_max_right c huv))
      (LipschitzWith.id.max_const c).lipschitzOnWith (by
        intro u hu
        simp only [uIcc_of_le (hsc.trans hct), mem_Icc] at hu
        simp only [uIcc_of_le hct, mem_Icc]
        exact ⟨le_max_right _ _, max_le hu.2 hct⟩)
  apply ((hl.add hr).sub
    (LipschitzWith.const (f c)).lipschitzOnWith.absolutelyContinuousOnInterval).congr
  intro u _
  simp only [Pi.sub_apply, Pi.add_apply]
  split_ifs with hu
  · simp only [min_eq_left hu, max_eq_right hu, he, add_sub_cancel_right]
  · simp only [min_eq_right (le_of_not_ge hu), max_eq_left (le_of_not_ge hu)]
    abel

/-- Horizontal curves meeting at an endpoint concatenate with piecewise controls. -/
theorem IsHorizontalCurveOn.append {N q : ℕ}
    {X : Fin q → (Fin N → ℝ) → (Fin N → ℝ)} {f g : ℝ → (Fin N → ℝ)}
    {a b : Fin q → ℝ → ℝ} {s c t : ℝ}
    (hf : IsHorizontalCurveOn X f a s c) (hg : IsHorizontalCurveOn X g b c t)
    (hsc : s ≤ c) (hct : c ≤ t) (he : f c = g c) :
    IsHorizontalCurveOn X (fun u => if u ≤ c then f u else g u)
      (fun i u => if u ≤ c then a i u else b i u) s t := by
  have hunion := Icc_union_Icc_eq_Icc hsc hct
  have hright : ∀ i, (fun u => if u ≤ c then a i u else b i u) =ᵐ[volume.restrict (Icc c t)] b i := by
    intro i
    filter_upwards [ae_restrict_mem measurableSet_Icc,
      (volume.restrict (Icc c t)).ae_ne c] with u hu hne
    simp [not_le.mpr (lt_of_le_of_ne hu.1 (Ne.symm hne))]
  refine ⟨absolutelyContinuousOnInterval_piecewise hsc hct hf.absolutelyContinuous
    hg.absolutelyContinuous he, ?_, ?_, ?_⟩
  · intro i
    rw [← hunion, aemeasurable_union_iff]
    constructor
    · apply (hf.aemeasurable i).congr
      filter_upwards [ae_restrict_mem measurableSet_Icc] with u hu
      simp [hu.2]
    · exact (hg.aemeasurable i).congr (hright i).symm
  · rw [← hunion, integrableOn_union]
    constructor
    · apply hf.integrable_norm.congr
      filter_upwards [ae_restrict_mem measurableSet_Icc] with u hu
      simp only [controlNorm, ite_eq_left hu.2]
    · apply hg.integrable_norm.congr
      filter_upwards [ae_restrict_mem measurableSet_Icc,
        (volume.restrict (Icc c t)).ae_ne c] with u hu hne
      simp only [controlNorm, ite_eq_right (not_le.mpr (lt_of_le_of_ne hu.1 (Ne.symm hne)))]
  · rw [← hunion, ae_restrict_union_iff]
    constructor
    · filter_upwards [hf.hasDerivAt, ae_restrict_mem measurableSet_Icc,
        (volume.restrict (Icc s c)).ae_ne c] with u hu humem hne
      have huc : u < c := lt_of_le_of_ne humem.2 hne
      have heq : (fun v => if v ≤ c then f v else g v) =ᶠ[𝓝 u] f := by
        filter_upwards [gt_mem_nhds huc] with v hv
        simp [hv.le]
      simpa only [ite_eq_left humem.2] using hu.congr_of_eventuallyEq heq
    · filter_upwards [hg.hasDerivAt, ae_restrict_mem measurableSet_Icc,
        (volume.restrict (Icc c t)).ae_ne c] with u hu humem hne
      have hcu : c < u := lt_of_le_of_ne humem.1 (Ne.symm hne)
      have heq : (fun v => if v ≤ c then f v else g v) =ᶠ[𝓝 u] g := by
        filter_upwards [lt_mem_nhds hcu] with v hv
        simp [not_le.mpr hv]
      simpa only [ite_eq_right (not_le.mpr hcu)] using hu.congr_of_eventuallyEq heq

end HeatKernel
