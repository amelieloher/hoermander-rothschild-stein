-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.S.CompactTestDerivativeBound
public import RothschildStein.S.CurveTestDerivative
public import RothschildStein.S.FlowPullbackSupport
public import Mathlib.MeasureTheory.Integral.DominatedConvergence

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public section
noncomputable section
open Set Filter MeasureTheory TopologicalSpace
open scoped Topology
namespace RothschildStein.S
variable {n : ℕ}

/-- The test pullback quotient converges under the local integral, with domination on a common compact neighborhood of the test support (BB Proposition 2.22, p. 89). -/
theorem tendsto_integral_flow_test_quotient
    (Ω : Opens (Fin n → ℝ)) (K C : Compacts (Fin n → ℝ))
    (hKΩ : (K : Set (Fin n → ℝ)) ⊆ Ω) (hCΩ : (C : Set (Fin n → ℝ)) ⊆ Ω)
    (hKC : (K : Set (Fin n → ℝ)) ⊆ C)
    (X : (Fin n → ℝ) → (Fin n → ℝ))
    (hX : ContDiffOn ℝ (⊤ : ℕ∞) X (Ω : Set (Fin n → ℝ)))
    {f : (Fin n → ℝ) → ℝ} (hf : ContinuousOn f (Ω : Set (Fin n → ℝ)))
    {U V : Set (Fin n → ℝ)} (hV : IsOpen V) (hVU : V ⊆ U)
    (hVΩ : V ⊆ Ω) (hKU : (K : Set (Fin n → ℝ)) ⊆ U)
    {τ δ : ℝ} (hδ : 0 < δ) (hδτ : δ < τ)
    (Φ : ((Fin n → ℝ) × ℝ) → (Fin n → ℝ))
    (hc : ContinuousOn Φ (U ×ˢ Ioo (-τ) τ))
    (hsol : ∀ x ∈ U,Φ (x,0) = x ∧ ∀ t ∈ Ioo (-τ) τ,
      HasDerivAt (fun v => Φ (x,v)) (X (Φ (x,t))) t ∧ Φ (x,t) ∈ Ω)
    (hC : ∀ x ∈ (K : Set (Fin n → ℝ)),∀ t ∈ Icc (-δ) δ,Φ (x,t) ∈ C)
    (φ : (Fin n → ℝ) → ℝ) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hs : tsupport φ ⊆ K) :
    Tendsto (fun t => ∫ x in V,f x*((φ (Φ (x,t))-φ x)/t)) (𝓝[≠] 0)
      (𝓝 (∫ x in V,f x*fieldDerivative X φ x)) := by
  obtain ⟨A,hA0,hA⟩ := exists_uniform_compact_test_field_derivative_bound Ω K hKΩ X hX φ hφ hs
  obtain ⟨F,hF⟩ := C.isCompact.exists_bound_of_continuousOn (hf.mono hCΩ)
  let B := (C : Set (Fin n → ℝ)).indicator (fun _ => max F 0 * A)
  have htime : Icc (-δ) δ ⊆ Ioo (-τ) τ := by
    intro t ht
    constructor <;> linarith [ht.1,ht.2]
  have hsmall : ∀ᶠ t in 𝓝[≠] (0 : ℝ),t ∈ Ioo (-δ) δ ∧ t ≠ 0 := by
    have hnear : ∀ᶠ t in 𝓝 (0 : ℝ),t ∈ Ioo (-δ) δ := isOpen_Ioo.mem_nhds ⟨by linarith,hδ⟩
    filter_upwards [hnear.filter_mono nhdsWithin_le_nhds,self_mem_nhdsWithin] with t ht hn
    exact ⟨ht,by simpa only [mem_compl_iff,mem_singleton_iff] using hn⟩
  apply tendsto_integral_filter_of_dominated_convergence B
  · filter_upwards [hsmall] with t ht
    have hflow : ContinuousOn (fun x => Φ (x,t)) V :=
      hc.comp (continuous_id.prodMk continuous_const).continuousOn
        (fun x hx => ⟨hVU hx,htime (Ioo_subset_Icc_self ht.1)⟩)
    exact ((hf.mono hVΩ).mul (((hφ.continuous.comp_continuousOn hflow).sub
      hφ.continuous.continuousOn).div_const t)).aestronglyMeasurable hV.measurableSet
  · filter_upwards [hsmall] with t ht
    filter_upwards [ae_restrict_mem hV.measurableSet] with x hx
    by_cases hxC : x ∈ (C : Set (Fin n → ℝ))
    · have hzero : (0 : ℝ) ∈ Icc (-δ) δ := ⟨by linarith,by linarith⟩
      have hsub : uIcc 0 t ⊆ Icc (-δ) δ := ordConnected_Icc.uIcc_subset hzero (Ioo_subset_Icc_self ht.1)
      have hQ := curve_test_difference_quotient_bound X φ (fun v => Φ (x,v)) ht.2
        (fun _ _ => hφ.differentiable (by simp) _)
        (fun s hs => ((hsol x (hVU hx)).2 s (htime (hsub hs))).1)
        (fun s hs => hA _ ((hsol x (hVU hx)).2 s (htime (hsub hs))).2)
      rw [(hsol x (hVU hx)).1] at hQ
      have hFb : |f x| ≤ max F 0 := by
        simpa only [Real.norm_eq_abs] using (hF x hxC).trans (le_max_left F 0)
      rw [Real.norm_eq_abs,abs_mul]
      change |f x| * |(φ (Φ (x,t))-φ x)/t| ≤ (C : Set (Fin n → ℝ)).indicator (fun _ => max F 0 * A) x
      rw [indicator_of_mem hxC]
      exact mul_le_mul hFb hQ (abs_nonneg _) (le_max_right F 0)
    · have hn : -t ∈ Icc (-δ) δ := by constructor <;> linarith [ht.1.1,ht.1.2]
      have hS := flow_test_difference_support_subset Ω.isOpen hX (hδ.trans hδτ) Φ hsol hKU hKC φ
        ((subset_tsupport φ).trans hs) (htime (Ioo_subset_Icc_self ht.1))
        (fun y hy => hC y hy (-t) hn)
      have hz : φ (Φ (x,t))-φ x = 0 := by
        by_contra hne
        exact hxC (hS ⟨hVU hx,hne⟩)
      simp only [hz,zero_div,mul_zero,norm_zero,B,indicator_of_notMem hxC]
      exact le_rfl
  · have hi : Integrable B volume :=
      (integrableOn_const (μ := volume) C.isCompact.measure_lt_top.ne).integrable_indicator C.isCompact.measurableSet
    exact hi.mono_measure Measure.restrict_le_self
  · filter_upwards [ae_restrict_mem hV.measurableSet] with x hx
    have hzero : (0 : ℝ) ∈ Ioo (-τ) τ := ⟨by linarith,by linarith⟩
    have H := curve_test_difference_quotient_tendsto X φ (fun v => Φ (x,v))
      (hφ.differentiable (by simp) _) ((hsol x (hVU hx)).2 0 hzero).1
    simpa only [(hsol x (hVU hx)).1] using tendsto_const_nhds.mul H

end RothschildStein.S
