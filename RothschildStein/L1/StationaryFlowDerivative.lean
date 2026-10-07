-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module
public import RothschildStein.G1.FlowVariational
@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set Filter
open scoped Topology
namespace RothschildStein.L1

set_option backward.defeqAttrib.useBackward true in
/-- For a stationary-parameter flow through a zero-field point,
the initial derivative is identity plus time times the coefficient frame.
This follows from the actual variational equation, whose spatial part is
zero; no parameter derivative is postulated (BB (10.15), p. 499). -/
theorem initialDerivative_of_stationary_flow
    {P E : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    {Ω U : Set (P × E)} (hΩ : IsOpen Ω) (hU : IsOpen U)
    {τ : ℝ} (hτ : 0 < τ) (F : (P × E) → (P × E))
    (hF : ContDiffOn ℝ (⊤ : ℕ∞) F Ω)
    (Ψ : ((P × E) × ℝ) → (P × E))
    (hΨ : ContDiffOn ℝ (⊤ : ℕ∞) Ψ (U ×ˢ Ioo (-τ) τ))
    (hinit : ∀ q ∈ U, Ψ (q,0) = q)
    (hsol : ∀ q ∈ U, ∀ t ∈ Ioo (-τ) τ,
      HasDerivAt (fun s => Ψ (q,s)) (F (Ψ (q,t))) t ∧ Ψ (q,t) ∈ Ω)
    (hstationary : ∀ q ∈ U, ∀ t ∈ Ioo (-τ) τ, (Ψ (q,t)).1 = q.1)
    (x : E) (hx : (0,x) ∈ U) (L : P →L[ℝ] E)
    (hfix : ∀ t ∈ Ioo (-τ) τ, Ψ ((0,x),t) = (0,x))
    (hD : fderiv ℝ F (0,x) =
      (0 : (P × E) →L[ℝ] P).prod (L.comp (ContinuousLinearMap.fst ℝ P E)))
    {t : ℝ} (ht : t ∈ Ioo (-τ) τ) :
    fderiv ℝ (fun q => Ψ (q,t)) (0,x) =
      ContinuousLinearMap.id ℝ (P × E) + t • fderiv ℝ F (0,x) := by
  let J : ℝ → (P × E) →L[ℝ] (P × E) := fun s => fderiv ℝ (fun q => Ψ (q,s)) (0,x)
  let A := fderiv ℝ F (0,x)
  have hzero : (0 : ℝ) ∈ Ioo (-τ) τ := ⟨by linarith,hτ⟩
  have hfirst : ∀ s ∈ Ioo (-τ) τ,
      (ContinuousLinearMap.fst ℝ P E).comp (J s) = ContinuousLinearMap.fst ℝ P E := by
    intro s hs
    have hd : DifferentiableAt ℝ (fun q => Ψ (q,s)) (0,x) :=
      ((hΨ.contDiffAt ((hU.prod isOpen_Ioo).mem_nhds ⟨hx,hs⟩)).comp (0,x)
        (contDiff_id.prodMk contDiff_const).contDiffAt).differentiableAt (by simp)
    have he : (fun q => (Ψ (q,s)).1) =ᶠ[𝓝 (0,x)] (fun q : P × E => q.1) := by
      filter_upwards [hU.mem_nhds hx] with q hq
      exact hstationary q hq s hs
    have hh := he.fderiv_eq (𝕜 := ℝ)
    change fderiv ℝ ((ContinuousLinearMap.fst ℝ P E) ∘ (fun q => Ψ (q,s))) (0,x) =
      fderiv ℝ (ContinuousLinearMap.fst ℝ P E) (0,x) at hh
    rw [fderiv_comp (0,x) (ContinuousLinearMap.fst ℝ P E).differentiableAt hd,
      ContinuousLinearMap.fderiv,ContinuousLinearMap.fderiv] at hh
    exact hh
  have hJA : ∀ s ∈ Ioo (-τ) τ, HasDerivAt J A s := by
    intro s hs
    have hh := G1.localFlow_variational_of_joint_contDiff hΩ hU hF Ψ hΨ hsol hx hs
    rw [hfix s hs] at hh
    have he : A.comp (J s) = A := by
      change (fderiv ℝ F (0,x)).comp (J s) = fderiv ℝ F (0,x)
      rw [hD]
      apply ContinuousLinearMap.ext
      intro v
      apply Prod.ext
      · rfl
      · change L ((J s v).1) = L v.1
        exact congrArg L (congrArg (fun B : (P × E) →L[ℝ] P => B v) (hfirst s hs))
    rwa [he] at hh
  have hJ0 : J 0 = ContinuousLinearMap.id ℝ (P × E) := by
    have he : (fun q => Ψ (q,0)) =ᶠ[𝓝 (0,x)] (fun q : P × E => q) := by
      filter_upwards [hU.mem_nhds hx] with q hq
      exact hinit q hq
    change fderiv ℝ (fun q => Ψ (q,0)) (0,x) = _
    rw [he.fderiv_eq]
    exact fderiv_fun_id
  have hd (s : ℝ) (hs : s ∈ Ioo (-τ) τ) :=
    (hJA s hs).fun_sub ((hasDerivAt_id s).smul_const A)
  have he := isOpen_Ioo.is_const_of_deriv_eq_zero isPreconnected_Ioo
    (fun s hs => (hd s hs).differentiableAt.differentiableWithinAt)
    (fun s hs => by simpa only [one_smul,sub_self,Pi.zero_apply,zero_apply] using (hd s hs).deriv) ht hzero
  simp only [id_eq] at he
  rw [zero_smul,sub_zero,hJ0] at he
  exact sub_eq_iff_eq_add.mp he
end RothschildStein.L1
