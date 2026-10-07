-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.S.FlowJacobianQuotientBound
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

/-- The inverse Jacobian quotient converges under the compact test integral. Continuity bounds the transported input on the common compact image, and the variational estimate gives a uniform Jacobian bound for dominated convergence (BB Proposition 2.22, (2.29)–(2.30), p. 90). -/
theorem tendsto_integral_inverse_flow_jacobian_quotient
    (Ω : Opens (Fin n → ℝ)) (K C : Compacts (Fin n → ℝ))
    (hKΩ : (K : Set (Fin n → ℝ)) ⊆ Ω) (hCΩ : (C : Set (Fin n → ℝ)) ⊆ Ω)
    (X : (Fin n → ℝ) → (Fin n → ℝ))
    (hX : ContDiffOn ℝ (⊤ : ℕ∞) X (Ω : Set (Fin n → ℝ)))
    {f : (Fin n → ℝ) → ℝ} (hf : ContinuousOn f (Ω : Set (Fin n → ℝ)))
    {U : Set (Fin n → ℝ)} (hU : IsOpen U) (hKU : (K : Set (Fin n → ℝ)) ⊆ U)
    {τ δ : ℝ} (hδ : 0 < δ) (hδτ : δ < τ)
    (Φ : ((Fin n → ℝ) × ℝ) → (Fin n → ℝ))
    (hjoint : ContDiffOn ℝ (⊤ : ℕ∞) Φ (U ×ˢ Ioo (-τ) τ))
    (hsol : ∀ x ∈ U,Φ (x,0) = x ∧ ∀ t ∈ Ioo (-τ) τ,
      HasDerivAt (fun v => Φ (x,v)) (X (Φ (x,t))) t ∧ Φ (x,t) ∈ Ω)
    (hC : ∀ x ∈ (K : Set (Fin n → ℝ)),∀ t ∈ Icc (-δ) δ,Φ (x,t) ∈ C)
    (φ : (Fin n → ℝ) → ℝ) (hφ : Continuous φ) :
    Tendsto (fun t => ∫ x in (K : Set (Fin n → ℝ)),f (Φ (x,-t))*φ x*
      (((fderiv ℝ (fun y => Φ (y,-t)) x).det-1)/t)) (𝓝[≠] 0)
      (𝓝 (∫ x in (K : Set (Fin n → ℝ)),f x*φ x*(-Hormander.Interface.euclideanDivergence X x))) := by
  obtain ⟨F,hF⟩ := C.isCompact.exists_bound_of_continuousOn (hf.mono hCΩ)
  obtain ⟨P,hP⟩ := K.isCompact.exists_bound_of_continuousOn hφ.continuousOn
  obtain ⟨M,hM0,hM⟩ := exists_uniform_inverse_jacobian_quotient_bound Ω.isOpen hU
    K.isCompact hKU hX hδ hδτ Φ hjoint hsol
  let B : ℝ := max F 0 * max P 0 * M
  have hτ : 0 < τ := hδ.trans hδτ
  have hzero : (0 : ℝ) ∈ Ioo (-τ) τ := ⟨by linarith,hτ⟩
  have htime : Icc (-δ) δ ⊆ Ioo (-τ) τ := by
    intro t ht
    constructor <;> linarith [ht.1,ht.2]
  have hsmall : ∀ᶠ t in 𝓝[≠] (0 : ℝ),t ∈ Ioo (-δ) δ ∧ t ≠ 0 := by
    have hnear : ∀ᶠ t in 𝓝 (0 : ℝ),t ∈ Ioo (-δ) δ := isOpen_Ioo.mem_nhds ⟨by linarith,hδ⟩
    filter_upwards [hnear.filter_mono nhdsWithin_le_nhds,self_mem_nhdsWithin] with t ht hn
    exact ⟨ht,by simpa only [mem_compl_iff,mem_singleton_iff] using hn⟩
  apply tendsto_integral_filter_of_dominated_convergence (fun _ => B)
  · filter_upwards [hsmall] with t ht
    have hn : -t ∈ Icc (-δ) δ := by constructor <;> linarith [ht.1.1,ht.1.2]
    have hp : ContinuousOn (fun x => (x,-t)) (K : Set (Fin n → ℝ)) :=
      (continuous_id.prodMk continuous_const).continuousOn
    have hm : MapsTo (fun x => (x,-t)) (K : Set (Fin n → ℝ)) (U ×ˢ Ioo (-τ) τ) :=
      fun x hx => ⟨hKU hx,htime hn⟩
    have hflow := hjoint.continuousOn.comp hp hm
    have hfc := hf.comp hflow (fun x hx => ((hsol x (hKU hx)).2 (-t) (htime hn)).2)
    have hJ := (continuousOn_flow_jacobian hU Φ hjoint).comp hp hm
    exact ((hfc.mul hφ.continuousOn).mul ((hJ.sub continuousOn_const).div_const t)).aestronglyMeasurable
      K.isCompact.measurableSet
  · filter_upwards [hsmall] with t ht
    filter_upwards [ae_restrict_mem K.isCompact.measurableSet] with x hx
    have hn : -t ∈ Icc (-δ) δ := by constructor <;> linarith [ht.1.1,ht.1.2]
    have hFb : |f (Φ (x,-t))| ≤ max F 0 := by
      simpa only [Real.norm_eq_abs] using (hF _ (hC x hx (-t) hn)).trans (le_max_left F 0)
    have hPb : |φ x| ≤ max P 0 := by
      simpa only [Real.norm_eq_abs] using (hP x hx).trans (le_max_left P 0)
    have hMb := hM x hx t (Ioo_subset_Icc_self ht.1) ht.2
    rw [Real.norm_eq_abs,abs_mul,abs_mul]
    exact mul_le_mul (mul_le_mul hFb hPb (abs_nonneg _) (le_max_right F 0)) hMb
      (abs_nonneg _) (mul_nonneg (le_max_right F 0) (le_max_right P 0))
  · exact integrableOn_const (μ := volume) K.isCompact.measure_lt_top.ne
  · filter_upwards [ae_restrict_mem K.isCompact.measurableSet] with x hx
    have hp : Tendsto (fun t : ℝ => (x,-t)) (𝓝 0) (𝓝 (x,0)) := by
      simpa only [neg_zero] using ((continuousAt_const (y := x) (x := (0 : ℝ))).prodMk continuousAt_neg).tendsto
    have hflow := (hjoint.continuousOn.continuousAt
      ((hU.prod isOpen_Ioo).mem_nhds ⟨hKU hx,hzero⟩)).tendsto.comp hp
    have hft : Tendsto (fun t => f (Φ (x,-t))) (𝓝[≠] 0) (𝓝 (f x)) := by
      have H := (hf.continuousAt (Ω.isOpen.mem_nhds (hKΩ hx))).tendsto.comp
        (by simpa only [(hsol x (hKU hx)).1] using hflow)
      exact H.mono_left nhdsWithin_le_nhds
    exact (hft.mul tendsto_const_nhds).mul
      (flow_inverse_jacobian_quotient_tendsto Ω.isOpen hU hX hτ Φ hjoint hsol (hKU hx))

end RothschildStein.S
