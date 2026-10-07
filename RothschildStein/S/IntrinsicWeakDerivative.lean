-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.S.CompactFlowChart
public import RothschildStein.S.FlowIntegralIdentity
public import RothschildStein.S.FlowTestIntegralLimit
public import RothschildStein.S.IntrinsicFlowIntegralLimit
public import RothschildStein.S.FlowJacobianIntegralLimit
public import RothschildStein.S.WeakDeriv

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public section
noncomputable section
open Set Filter MeasureTheory TopologicalSpace
open scoped Topology
namespace RothschildStein.S
variable {n : ℕ}

/-- Every continuous intrinsic derivative of a continuous function is its weak derivative for any smooth local field (BB Proposition 2.22, pp. 87–90, equation (2.27)). -/
theorem hasWeakWordDeriv_of_intrinsic_derivative
    (Ω : Opens (Fin n → ℝ)) (X : (Fin n → ℝ) → (Fin n → ℝ))
    (hX : ContDiffOn ℝ (⊤ : ℕ∞) X (Ω : Set (Fin n → ℝ)))
    (f g : (Fin n → ℝ) → ℝ)
    (hf : ContinuousOn f (Ω : Set (Fin n → ℝ)))
    (hg : ContinuousOn g (Ω : Set (Fin n → ℝ)))
    (hfg : hasIntrinsicDeriv Ω X f g) :
    hasWeakWordDeriv (fun _ : Fin 1 => X) Ω [0] f g := by
  refine ⟨hf.locallyIntegrableOn Ω.isOpen.measurableSet,
    hg.locallyIntegrableOn Ω.isOpen.measurableSet,?_⟩
  intro φ
  let K : Compacts (Fin n → ℝ) := ⟨tsupport φ,φ.hasCompactSupport⟩
  have hKΩ : (K : Set (Fin n → ℝ)) ⊆ Ω := φ.tsupport_subset
  obtain ⟨τ,hτ,U,V,hU,hV,hKV,hVU,hUΩ,Φ,hjoint,hsol,δ,hδ,hδτ,hstay,hback,_,_,_,_⟩ :=
    exists_compact_flow_chart Ω K hKΩ X hX
  have hKU := hKV.trans hVU
  have hVΩ := hVU.trans hUΩ
  have hsol' : ∀ x ∈ U,Φ (x,0) = x ∧ ∀ t ∈ Ioo (-τ) τ,
      HasDerivAt (fun v => Φ (x,v)) (X (Φ (x,t))) t ∧ Φ (x,t) ∈ Ω :=
    fun x hx => ⟨(hsol x hx).1,fun t ht => ((hsol x hx).2 t ht).symm⟩
  have htime : Icc (-δ) δ ⊆ Ioo (-τ) τ := by
    intro t ht
    constructor <;> linarith [ht.1,ht.2]
  have hct : ContinuousOn Φ ((K : Set (Fin n → ℝ)) ×ˢ Icc (-δ) δ) :=
    hjoint.continuousOn.mono (Set.prod_mono hKU htime)
  let C : Compacts (Fin n → ℝ) := ⟨Φ '' ((K : Set (Fin n → ℝ)) ×ˢ Icc (-δ) δ),
    (K.isCompact.prod isCompact_Icc).image_of_continuousOn hct⟩
  have hCV : (C : Set (Fin n → ℝ)) ⊆ V := by
    rintro _ ⟨⟨x,t⟩,⟨hx,ht⟩,rfl⟩
    exact hback x hx t ht
  have hCΩ := hCV.trans hVΩ
  have hKC : (K : Set (Fin n → ℝ)) ⊆ C := by
    intro x hx
    exact ⟨(x,0),⟨hx,by constructor <;> linarith⟩,(hsol x (hKU hx)).1⟩
  have hC : ∀ x ∈ (K : Set (Fin n → ℝ)),∀ t ∈ Icc (-δ) δ,Φ (x,t) ∈ C :=
    fun x hx t ht => ⟨(x,t),⟨hx,ht⟩,rfl⟩
  have hs : tsupport (φ : (Fin n → ℝ) → ℝ) ⊆ K := Subset.rfl
  have hs' := (subset_tsupport (φ : (Fin n → ℝ) → ℝ)).trans hs
  have hL := tendsto_integral_flow_test_quotient Ω K C hKΩ hCΩ hKC X hX hf
    hV hVU hVΩ hKU hδ hδτ Φ hjoint.continuousOn hsol' hC φ φ.contDiff hs
  have hR1 := tendsto_integral_intrinsic_inverse_flow_quotient Ω K C hKΩ hCΩ X hf hg hfg
    hKU hδ hδτ Φ hjoint.continuousOn hsol' hC φ φ.continuous
  have hR2 := tendsto_integral_inverse_flow_jacobian_quotient Ω K C hKΩ hCΩ X hX hf
    hU hKU hδ hδτ Φ hjoint hsol' hC φ φ.continuous
  have heq : (fun t => ∫ x in V,f x*((φ (Φ (x,t))-φ x)/t)) =ᶠ[𝓝[≠] 0]
      (fun t => (∫ x in (K : Set (Fin n → ℝ)),((f (Φ (x,-t))-f x)/t)*φ x) +
        ∫ x in (K : Set (Fin n → ℝ)),f (Φ (x,-t))*φ x*
          (((fderiv ℝ (fun y => Φ (y,-t)) x).det-1)/t)) := by
    have hnear : ∀ᶠ t in 𝓝 (0 : ℝ),t ∈ Ioo (-δ) δ := isOpen_Ioo.mem_nhds ⟨by linarith,hδ⟩
    filter_upwards [hnear.filter_mono nhdsWithin_le_nhds] with t ht
    have hn : -t ∈ Icc (-δ) δ := by constructor <;> linarith [ht.1,ht.2]
    exact integral_flow_test_quotient_identity Ω K C hU hV hKV hVU hVΩ hCV hKC X hX hτ
      Φ hjoint hsol' (htime (Ioo_subset_Icc_self ht))
      (fun x hx => hstay x hx t (Ioo_subset_Icc_self ht))
      (fun x hx => hback x hx (-t) hn) (fun x hx => hC x hx (-t) hn)
      f φ hf φ.continuous hs'
  have hbalance := tendsto_nhds_unique hL ((hR1.add hR2).congr' heq.symm)
  have hLeftK : (∫ x in V,f x*fieldDerivative X φ x) =
      ∫ x in (K : Set (Fin n → ℝ)),f x*fieldDerivative X φ x := by
    apply setIntegral_eq_of_subset_of_forall_sdiff_eq_zero hV.measurableSet hKV
    intro x hx
    have hz : fieldDerivative X φ x = 0 := image_eq_zero_of_notMem_tsupport
      (fun hy => hx.2 (hs (tsupport_fieldDerivative_subset X φ hy)))
    rw [hz,mul_zero]
  rw [hLeftK] at hbalance
  have hng : (∫ x in (K : Set (Fin n → ℝ)),(-g x)*φ x) =
      -(∫ x in (K : Set (Fin n → ℝ)),g x*φ x) := by
    simp_rw [neg_mul]
    rw [integral_neg]
  have hnd : (∫ x in (K : Set (Fin n → ℝ)),f x*φ x*(-Hormander.Interface.euclideanDivergence X x)) =
      -(∫ x in (K : Set (Fin n → ℝ)),f x*φ x*Hormander.Interface.euclideanDivergence X x) := by
    simp_rw [mul_neg]
    rw [integral_neg]
  rw [hng,hnd] at hbalance
  have hGΩ : (∫ x in (Ω : Set (Fin n → ℝ)),g x*φ x) =
      ∫ x in (K : Set (Fin n → ℝ)),g x*φ x := by
    apply setIntegral_eq_of_subset_of_forall_sdiff_eq_zero Ω.isOpen.measurableSet hKΩ
    intro x hx
    have hz : φ x = 0 := image_eq_zero_of_notMem_tsupport hx.2
    rw [hz,mul_zero]
  have hTΩ : (∫ x in (Ω : Set (Fin n → ℝ)),f x*fieldTranspose X φ x) =
      ∫ x in (K : Set (Fin n → ℝ)),f x*fieldTranspose X φ x := by
    apply setIntegral_eq_of_subset_of_forall_sdiff_eq_zero Ω.isOpen.measurableSet hKΩ
    intro x hx
    have hz : fieldTranspose X φ x = 0 := image_eq_zero_of_notMem_tsupport
      (fun hy => hx.2 (hs (tsupport_fieldTranspose_subset X φ hy)))
    rw [hz,mul_zero]
  have hi1 := ((hf.mono hKΩ).mul
    ((contDiffOn_fieldDerivative Ω X φ hX φ.contDiff.contDiffOn).continuousOn.mono hKΩ)).integrableOn_compact (μ := volume) K.isCompact
  have hi2 := (((hf.mono hKΩ).mul φ.continuous.continuousOn).mul
    ((continuousOn_smooth_field_divergence Ω.isOpen X hX).mono hKΩ)).integrableOn_compact (μ := volume) K.isCompact
  change (∫ x in (Ω : Set (Fin n → ℝ)),g x*φ x) =
    ∫ x in (Ω : Set (Fin n → ℝ)),f x*fieldTranspose X φ x
  rw [hGΩ,hTΩ]
  have hForm : (∫ x in (K : Set (Fin n → ℝ)),f x*fieldTranspose X φ x) =
      -(∫ x in (K : Set (Fin n → ℝ)),f x*fieldDerivative X φ x) -
        (∫ x in (K : Set (Fin n → ℝ)),f x*φ x*Hormander.Interface.euclideanDivergence X x) := by
    calc
      _ = ∫ x in (K : Set (Fin n → ℝ)),-(f x*fieldDerivative X φ x)-
          f x*φ x*Hormander.Interface.euclideanDivergence X x := by
        apply setIntegral_congr_fun K.isCompact.measurableSet
        intro x hx
        dsimp only
        rw [fieldTranspose_formula X φ x
          ((hX.contDiffAt (Ω.isOpen.mem_nhds (hKΩ hx))).differentiableAt (by simp))
          (φ.contDiff.differentiable (by simp) x)]
        ring
      _ = _ := by
        rw [integral_sub (f := fun x => -(f x*fieldDerivative X φ x))
          (g := fun x => f x*φ x*Hormander.Interface.euclideanDivergence X x) hi1.neg hi2,integral_neg]
  rw [hForm]
  linarith

end RothschildStein.S
