-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module
public import RothschildStein.L1.SmoothFrameFlow
public import RothschildStein.L1.StationaryFlowDerivative
@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set
open scoped Topology
namespace RothschildStein.L1

/-- The joint coefficient/initial-point derivative of the actual
frame flow at zero coefficients is spatial identity plus time times the
frame. All hypotheses are the actual smooth-flow and ODE data. -/
theorem frameFlow_derivative_of_flow {d N : ℕ}
    {Ω : Set (Fin N → ℝ)} {U : Set ((Fin d → ℝ) × (Fin N → ℝ))}
    (hΩ : IsOpen Ω) (hU : IsOpen U) {τ : ℝ} (hτ : 0 < τ)
    (Y : Fin d → (Fin N → ℝ) → (Fin N → ℝ))
    (hY : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (Y i) Ω)
    (Φ : (((Fin d → ℝ) × (Fin N → ℝ)) × ℝ) → (Fin N → ℝ))
    (hΦ : ContDiffOn ℝ (⊤ : ℕ∞) Φ (U ×ˢ Ioo (-τ) τ))
    (hinit : ∀ q ∈ U, Φ (q,0) = q.2)
    (hsol : ∀ q ∈ U, ∀ t ∈ Ioo (-τ) τ, Φ (q,t) ∈ Ω ∧
      HasDerivAt (fun s => Φ (q,s)) (frameCoefficientField Y (q.1,Φ (q,t))) t)
    (x : Fin N → ℝ) (hx : (0,x) ∈ U)
    (hfix : ∀ t ∈ Ioo (-τ) τ, Φ ((0,x),t) = x)
    {t : ℝ} (ht : t ∈ Ioo (-τ) τ) (v : Fin d → ℝ) (w : Fin N → ℝ) :
    fderiv ℝ (fun q => Φ (q,t)) (0,x) (v,w) = w + t • frameValueCLM Y x v := by
  let F : ((Fin d → ℝ) × (Fin N → ℝ)) → ((Fin d → ℝ) × (Fin N → ℝ)) :=
    fun q => (0,frameCoefficientField Y q)
  let Ψ : (((Fin d → ℝ) × (Fin N → ℝ)) × ℝ) → ((Fin d → ℝ) × (Fin N → ℝ)) :=
    fun q => (q.1.1,Φ q)
  have hF : ContDiffOn ℝ (⊤ : ℕ∞) F (univ ×ˢ Ω) :=
    contDiffOn_const.prodMk (frameCoefficientField_contDiffOn Y hY)
  have hΨ : ContDiffOn ℝ (⊤ : ℕ∞) Ψ (U ×ˢ Ioo (-τ) τ) :=
    (contDiff_fst.fst).contDiffOn.prodMk hΦ
  have hinitΨ : ∀ q ∈ U, Ψ (q,0) = q := by
    intro q hq
    exact Prod.ext rfl (hinit q hq)
  have hsolΨ : ∀ q ∈ U, ∀ s ∈ Ioo (-τ) τ,
      HasDerivAt (fun z => Ψ (q,z)) (F (Ψ (q,s))) s ∧ Ψ (q,s) ∈ univ ×ˢ Ω := by
    intro q hq s hs
    exact ⟨(hasDerivAt_const s q.1).prodMk ((hsol q hq s hs).2),
      ⟨mem_univ _,(hsol q hq s hs).1⟩⟩
  have hxΩ : x ∈ Ω := by
    have h0 : (0 : ℝ) ∈ Ioo (-τ) τ := ⟨by linarith,hτ⟩
    simpa only [hfix 0 h0] using (hsol (0,x) hx 0 h0).1
  have hdF : fderiv ℝ F (0,x) =
      (0 : ((Fin d → ℝ) × (Fin N → ℝ)) →L[ℝ] (Fin d → ℝ)).prod
        ((frameValueCLM Y x).comp (ContinuousLinearMap.fst ℝ _ _)) :=
    ((hasFDerivAt_const (0 : Fin d → ℝ) ((0 : Fin d → ℝ),x)).prodMk
      (frameCoefficientField_hasFDerivAt_zero Y x
        (fun i => ((hY i).contDiffAt (hΩ.mem_nhds hxΩ)).differentiableAt (by simp)))).fderiv
  have he := initialDerivative_of_stationary_flow (isOpen_univ.prod hΩ) hU hτ F hF Ψ hΨ
    hinitΨ hsolΨ (fun _ _ _ _ => rfl) x hx (frameValueCLM Y x)
    (fun s hs => Prod.ext rfl (hfix s hs)) hdF ht
  have hdiff : DifferentiableAt ℝ (fun q => Ψ (q,t)) (0,x) :=
    ((hΨ.contDiffAt ((hU.prod isOpen_Ioo).mem_nhds ⟨hx,ht⟩)).comp (0,x)
      (contDiff_id.prodMk contDiff_const).contDiffAt).differentiableAt (by simp)
  have hs := (ContinuousLinearMap.snd ℝ (Fin d → ℝ) (Fin N → ℝ)).hasFDerivAt.comp (0,x) hdiff.hasFDerivAt
  change HasFDerivAt (fun q => Φ (q,t))
    ((ContinuousLinearMap.snd ℝ _ _).comp (fderiv ℝ (fun q => Ψ (q,t)) (0,x))) (0,x) at hs
  rw [hs.fderiv,ContinuousLinearMap.comp_apply]
  have hv := congrArg (fun A : ((Fin d → ℝ) × (Fin N → ℝ)) →L[ℝ]
      ((Fin d → ℝ) × (Fin N → ℝ)) => (A (v,w)).2) he
  simpa only [hdF,add_apply,ContinuousLinearMap.id_apply,
    smul_apply,ContinuousLinearMap.prod_apply,
    ContinuousLinearMap.comp_apply,ContinuousLinearMap.coe_fst',Prod.snd_add,
    Prod.snd_smul,Prod.smul_mk,ContinuousLinearMap.coe_snd'] using hv
/-- The derivative formula as a continuous linear map, ready for
composition with the canonical coefficient rescaling. -/
theorem frameFlow_hasFDerivAt_of_flow {N : ℕ}
    {Ω : Set (Fin N → ℝ)} {U : Set ((Fin N → ℝ) × (Fin N → ℝ))}
    (hΩ : IsOpen Ω) (hU : IsOpen U) {τ : ℝ} (hτ : 0 < τ)
    (Y : Fin N → (Fin N → ℝ) → (Fin N → ℝ))
    (hY : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (Y i) Ω)
    (Φ : (((Fin N → ℝ) × (Fin N → ℝ)) × ℝ) → (Fin N → ℝ))
    (hΦ : ContDiffOn ℝ (⊤ : ℕ∞) Φ (U ×ˢ Ioo (-τ) τ))
    (hinit : ∀ q ∈ U, Φ (q,0) = q.2)
    (hsol : ∀ q ∈ U, ∀ t ∈ Ioo (-τ) τ, Φ (q,t) ∈ Ω ∧
      HasDerivAt (fun s => Φ (q,s)) (frameCoefficientField Y (q.1,Φ (q,t))) t)
    (x : Fin N → ℝ) (hx : (0,x) ∈ U)
    (hfix : ∀ t ∈ Ioo (-τ) τ, Φ ((0,x),t) = x)
    {t : ℝ} (ht : t ∈ Ioo (-τ) τ) :
    HasFDerivAt (fun q => Φ (q,t))
      ((t • frameValueCLM Y x).coprod (ContinuousLinearMap.id ℝ _)) (0,x) := by
  have hd : DifferentiableAt ℝ (fun q => Φ (q,t)) (0,x) :=
    ((hΦ.contDiffAt ((hU.prod isOpen_Ioo).mem_nhds ⟨hx,ht⟩)).comp (0,x)
      (contDiff_id.prodMk contDiff_const).contDiffAt).differentiableAt (by simp)
  have he : fderiv ℝ (fun q => Φ (q,t)) (0,x) =
      (t • frameValueCLM Y x).coprod (ContinuousLinearMap.id ℝ _) := by
    apply ContinuousLinearMap.ext
    intro q
    rw [frameFlow_derivative_of_flow hΩ hU hτ Y hY Φ hΦ hinit hsol x hx hfix ht q.1 q.2]
    simp [add_comm]
  rw [← he]
  exact hd.hasFDerivAt
end RothschildStein.L1
