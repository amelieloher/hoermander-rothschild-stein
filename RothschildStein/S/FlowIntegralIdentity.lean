-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.S.CompactFlowChangeVariables
public import RothschildStein.S.FlowJacobianContinuity
public import RothschildStein.S.FlowPullbackSupport

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public section
noncomputable section
open Set MeasureTheory TopologicalSpace
namespace RothschildStein.S
variable {n : ℕ}

/-- The finite-time pullback quotient splits into the
intrinsic inverse-flow quotient and the inverse Jacobian quotient. All
integrability needed for subtracting and adding integrals follows from
continuity and the compact chart buffer (BB Prop 2.22, p. 90, equation (4)). -/
theorem integral_flow_test_quotient_identity
    (Ω : Opens (Fin n → ℝ)) (K C : Compacts (Fin n → ℝ))
    {U V : Set (Fin n → ℝ)} (hU : IsOpen U) (hV : IsOpen V)
    (hKV : (K : Set (Fin n → ℝ)) ⊆ V) (hVU : V ⊆ U) (hVΩ : V ⊆ Ω)
    (hCV : (C : Set (Fin n → ℝ)) ⊆ V) (hKC : (K : Set (Fin n → ℝ)) ⊆ C)
    (X : (Fin n → ℝ) → (Fin n → ℝ))
    (hX : ContDiffOn ℝ (⊤ : ℕ∞) X (Ω : Set (Fin n → ℝ)))
    {τ : ℝ} (hτ : 0 < τ)
    (Φ : ((Fin n → ℝ) × ℝ) → (Fin n → ℝ))
    (hjoint : ContDiffOn ℝ (⊤ : ℕ∞) Φ (U ×ˢ Ioo (-τ) τ))
    (hsol : ∀ x ∈ U,Φ (x,0) = x ∧ ∀ t ∈ Ioo (-τ) τ,
      HasDerivAt (fun v => Φ (x,v)) (X (Φ (x,t))) t ∧ Φ (x,t) ∈ Ω)
    {t : ℝ} (ht : t ∈ Ioo (-τ) τ)
    (hstay : ∀ x ∈ V,Φ (x,t) ∈ U)
    (hback : ∀ x ∈ (K : Set (Fin n → ℝ)),Φ (x,-t) ∈ V)
    (hC : ∀ x ∈ (K : Set (Fin n → ℝ)),Φ (x,-t) ∈ C)
    (f φ : (Fin n → ℝ) → ℝ) (hf : ContinuousOn f (Ω : Set (Fin n → ℝ)))
    (hφ : Continuous φ) (hs : Function.support φ ⊆ K) :
    (∫ x in V,f x*((φ (Φ (x,t))-φ x)/t)) =
      (∫ x in (K : Set (Fin n → ℝ)),((f (Φ (x,-t))-f x)/t)*φ x) +
      ∫ x in (K : Set (Fin n → ℝ)),f (Φ (x,-t))*φ x*
        (((fderiv ℝ (fun y => Φ (y,-t)) x).det-1)/t) := by
  have hKU := hKV.trans hVU
  have hKΩ := hKV.trans hVΩ
  have hneg : -t ∈ Ioo (-τ) τ := ⟨by linarith [ht.2],by linarith [ht.1]⟩
  have hflow : ContinuousOn (fun x => Φ (x,t)) V :=
    hjoint.continuousOn.comp (continuous_id.prodMk continuous_const).continuousOn
      (fun x hx => ⟨hVU hx,ht⟩)
  have hc0 : ContinuousOn (fun x => f x*φ x) V := (hf.mono hVΩ).mul hφ.continuousOn
  have hct : ContinuousOn (fun x => f x*φ (Φ (x,t))) V :=
    (hf.mono hVΩ).mul (hφ.comp_continuousOn hflow)
  have hi0 : IntegrableOn (fun x => f x*φ x) V :=
    ((hc0.mono hCV).integrableOn_compact C.isCompact).of_forall_sdiff_eq_zero hV.measurableSet (by
      intro x hx
      have hz : φ x = 0 := by
        by_contra hn
        exact hx.2 (hKC (hs hn))
      rw [hz,mul_zero])
  have hit : IntegrableOn (fun x => f x*φ (Φ (x,t))) V :=
    ((hct.mono hCV).integrableOn_compact C.isCompact).of_forall_sdiff_eq_zero hV.measurableSet (by
      intro x hx
      have hz : φ (Φ (x,t)) = 0 := by
        by_contra hn
        exact hx.2 (flow_pullback_support_subset Ω.isOpen hX hτ Φ hsol hKU φ hs ht hC ⟨hVU hx.1,hn⟩)
      rw [hz,mul_zero])
  have hbase : (∫ x in V,f x*φ x) = ∫ x in (K : Set (Fin n → ℝ)),f x*φ x := by
    apply setIntegral_eq_of_subset_of_forall_sdiff_eq_zero hV.measurableSet hKV
    intro x hx
    have hz : φ x = 0 := by by_contra hn; exact hx.2 (hs hn)
    rw [hz,mul_zero]
  have hchange := integral_flow_pullback_eq_integral_on_support Ω.isOpen hU hV hVU hKU
    hX hτ Φ hjoint hsol ht hstay hback f φ hs
  have hchange' : (∫ x in V,f x*φ (Φ (x,t))) =
      ∫ x in (K : Set (Fin n → ℝ)),(fderiv ℝ (fun y => Φ (y,-t)) x).det*f (Φ (x,-t))*φ x := by
    refine hchange.trans (setIntegral_congr_fun K.isCompact.measurableSet ?_)
    intro x hx
    dsimp only
    rw [abs_of_pos (flow_jacobian_pos Ω.isOpen hU hX hτ Φ hjoint hsol (hKU hx) hneg)]
  have hp : ContinuousOn (fun x => (x,-t)) (K : Set (Fin n → ℝ)) :=
    (continuous_id.prodMk continuous_const).continuousOn
  have hm : MapsTo (fun x => (x,-t)) (K : Set (Fin n → ℝ)) (U ×ˢ Ioo (-τ) τ) :=
    fun x hx => ⟨hKU hx,hneg⟩
  have hfc := hf.comp (hjoint.continuousOn.comp hp hm)
    (fun x hx => ((hsol x (hKU hx)).2 (-t) hneg).2)
  have hJ := (continuousOn_flow_jacobian hU Φ hjoint).comp hp hm
  have hiQ := (((hfc.sub (hf.mono hKΩ)).div_const t).mul hφ.continuousOn).integrableOn_compact (μ := volume) K.isCompact
  have hiJ := ((hfc.mul hφ.continuousOn).mul ((hJ.sub (continuousOn_const (c := (1 : ℝ)))).div_const t)).integrableOn_compact (μ := volume) K.isCompact
  have hiProd : IntegrableOn (fun x => (fderiv ℝ (fun y => Φ (y,-t)) x).det*f (Φ (x,-t))*φ x)
      (K : Set (Fin n → ℝ)) volume := ((hJ.mul hfc).mul hφ.continuousOn).integrableOn_compact (μ := volume) K.isCompact
  have hiBase : IntegrableOn (fun x => f x*φ x) (K : Set (Fin n → ℝ)) volume := ((hf.mono hKΩ).mul hφ.continuousOn).integrableOn_compact (μ := volume) K.isCompact
  calc
    (∫ x in V,f x*((φ (Φ (x,t))-φ x)/t)) =
        ∫ x in V,(f x*φ (Φ (x,t))-f x*φ x)/t := by
      apply setIntegral_congr_fun hV.measurableSet
      intro x _
      ring
    _ = ((∫ x in V,f x*φ (Φ (x,t))) - (∫ x in V,f x*φ x))/t := by
      rw [integral_div,integral_sub hit hi0]
    _ = ((∫ x in (K : Set (Fin n → ℝ)),(fderiv ℝ (fun y => Φ (y,-t)) x).det*f (Φ (x,-t))*φ x) -
        (∫ x in (K : Set (Fin n → ℝ)),f x*φ x))/t := by rw [hchange',hbase]
    _ = ∫ x in (K : Set (Fin n → ℝ)),
        ((fderiv ℝ (fun y => Φ (y,-t)) x).det*f (Φ (x,-t))*φ x-f x*φ x)/t := by
      rw [integral_div,integral_sub hiProd hiBase]
    _ = ∫ x in (K : Set (Fin n → ℝ)),((f (Φ (x,-t))-f x)/t)*φ x +
        f (Φ (x,-t))*φ x*(((fderiv ℝ (fun y => Φ (y,-t)) x).det-1)/t) := by
      apply setIntegral_congr_fun K.isCompact.measurableSet
      intro x _
      ring
    _ = _ := integral_add hiQ hiJ

end RothschildStein.S
