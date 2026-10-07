-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.S.IntrinsicFlowQuotient
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

/-- The intrinsic inverse-flow quotient converges under
the compact-support integral. All measurability and domination premises
are discharged using the actual flow, continuous input and derivative,
and the common compact image buffer (BB Prop 2.22, p. 90). -/
theorem tendsto_integral_intrinsic_inverse_flow_quotient
    (Ω : Opens (Fin n → ℝ)) (K C : Compacts (Fin n → ℝ))
    (hKΩ : (K : Set (Fin n → ℝ)) ⊆ Ω) (hCΩ : (C : Set (Fin n → ℝ)) ⊆ Ω)
    (X : (Fin n → ℝ) → (Fin n → ℝ))
    {f g : (Fin n → ℝ) → ℝ}
    (hf : ContinuousOn f (Ω : Set (Fin n → ℝ)))
    (hg : ContinuousOn g (Ω : Set (Fin n → ℝ)))
    (hfg : hasIntrinsicDeriv Ω X f g)
    {U : Set (Fin n → ℝ)} (hKU : (K : Set (Fin n → ℝ)) ⊆ U)
    {τ δ : ℝ} (hδ : 0 < δ) (hδτ : δ < τ)
    (Φ : ((Fin n → ℝ) × ℝ) → (Fin n → ℝ))
    (hc : ContinuousOn Φ (U ×ˢ Ioo (-τ) τ))
    (hsol : ∀ x ∈ U,Φ (x,0) = x ∧ ∀ t ∈ Ioo (-τ) τ,
      HasDerivAt (fun v => Φ (x,v)) (X (Φ (x,t))) t ∧ Φ (x,t) ∈ Ω)
    (hC : ∀ x ∈ (K : Set (Fin n → ℝ)),∀ t ∈ Icc (-δ) δ,Φ (x,t) ∈ C)
    (φ : (Fin n → ℝ) → ℝ) (hφ : Continuous φ) :
    Tendsto (fun t => ∫ x in (K : Set (Fin n → ℝ)),
      ((f (Φ (x,-t))-f x)/t)*φ x) (𝓝[≠] 0)
      (𝓝 (∫ x in (K : Set (Fin n → ℝ)),(-g x)*φ x)) := by
  obtain ⟨G,hG⟩ := C.isCompact.exists_bound_of_continuousOn (hg.mono hCΩ)
  obtain ⟨P,hP⟩ := K.isCompact.exists_bound_of_continuousOn hφ.continuousOn
  let B : ℝ := max G 0 * max P 0
  have htime : Icc (-δ) δ ⊆ Ioo (-τ) τ := by
    intro t ht
    constructor <;> linarith [ht.1,ht.2]
  have hsmall : ∀ᶠ t in 𝓝[≠] (0 : ℝ),t ∈ Ioo (-δ) δ ∧ t ≠ 0 := by
    have hnear : ∀ᶠ t in 𝓝 (0 : ℝ),t ∈ Ioo (-δ) δ :=
      isOpen_Ioo.mem_nhds ⟨by linarith,hδ⟩
    filter_upwards [hnear.filter_mono nhdsWithin_le_nhds,self_mem_nhdsWithin] with t ht hn
    exact ⟨ht,by simpa only [mem_compl_iff,mem_singleton_iff] using hn⟩
  apply tendsto_integral_filter_of_dominated_convergence (fun _ => B)
  · filter_upwards [hsmall] with t ht
    have hn : -t ∈ Icc (-δ) δ := by constructor <;> linarith [ht.1.1,ht.1.2]
    have hflow : ContinuousOn (fun x => Φ (x,-t)) (K : Set (Fin n → ℝ)) :=
      hc.comp (continuous_id.prodMk continuous_const).continuousOn (fun x hx => ⟨hKU hx,htime hn⟩)
    have hfc : ContinuousOn (fun x => f (Φ (x,-t))) (K : Set (Fin n → ℝ)) :=
      hf.comp hflow (fun x hx => ((hsol x (hKU hx)).2 (-t) (htime hn)).2)
    exact (((hfc.sub (hf.mono hKΩ)).div_const t).mul hφ.continuousOn).aestronglyMeasurable
      K.isCompact.measurableSet
  · filter_upwards [hsmall] with t ht
    filter_upwards [ae_restrict_mem K.isCompact.measurableSet] with x hx
    have hn : -t ∈ Icc (-δ) δ := by constructor <;> linarith [ht.1.1,ht.1.2]
    have hzero : (0 : ℝ) ∈ Icc (-δ) δ := ⟨by linarith,by linarith⟩
    have hsub : uIcc 0 (-t) ⊆ Icc (-δ) δ := ordConnected_Icc.uIcc_subset hzero hn
    have hQ := intrinsic_curve_difference_quotient_bound Ω X hfg (fun v => Φ (x,v))
      (neg_ne_zero.mpr ht.2)
      (fun s hs => flow_isIntegralCurveAt X Φ x (fun v hv => ((hsol x (hKU hx)).2 v hv).1)
        (htime (hsub hs)))
      (fun s hs => ((hsol x (hKU hx)).2 s (htime (hsub hs))).2)
      (fun s hs => by
        simpa only [Real.norm_eq_abs] using (hG (Φ (x,s)) (hC x hx s (hsub hs))).trans (le_max_left G 0))
    have hQ' : |(f (Φ (x,-t))-f x)/t| ≤ max G 0 := by
      simpa only [(hsol x (hKU hx)).1,div_neg,abs_neg] using hQ
    have hP' : |φ x| ≤ max P 0 := by
      simpa only [Real.norm_eq_abs] using (hP x hx).trans (le_max_left P 0)
    rw [Real.norm_eq_abs,abs_mul]
    exact mul_le_mul hQ' hP' (abs_nonneg _) (le_max_right G 0)
  · exact integrableOn_const (μ := volume) K.isCompact.measure_lt_top.ne
  · filter_upwards [ae_restrict_mem K.isCompact.measurableSet] with x hx
    have hzero : (0 : ℝ) ∈ Ioo (-τ) τ := ⟨by linarith,by linarith⟩
    have H := intrinsic_curve_inverse_quotient_tendsto Ω X hfg (fun v => Φ (x,v))
      (flow_isIntegralCurveAt X Φ x (fun v hv => ((hsol x (hKU hx)).2 v hv).1) hzero)
      (by simpa only [(hsol x (hKU hx)).1] using hKΩ hx)
    simpa only [(hsol x (hKU hx)).1] using H.mul tendsto_const_nhds

end RothschildStein.S
