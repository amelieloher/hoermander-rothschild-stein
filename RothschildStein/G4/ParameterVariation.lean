-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.G1.FlowVariational
public import RothschildStein.G1.SmoothDependenceParameters
public import RothschildStein.G4.ParameterFlowSmoothness

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set Filter
open scoped Topology

namespace RothschildStein.G4

/-- The actual parameter derivative satisfies its variational
ODE. This is the first step of the exponential parameter derivative formula;
joint smoothness is the required hypothesis (BB Lemma 9.48, pp. 441–442). -/
theorem parameterFlow_variational_of_joint_contDiff {P E : Type*}
    [NormedAddCommGroup P] [NormedSpace ℝ P] [NormedAddCommGroup E] [NormedSpace ℝ E]
    {A : Set P} {Ω : Set E} {U : Set (P × E)}
    (hA : IsOpen A) (hΩ : IsOpen Ω) (hU : IsOpen U) (hUA : U ⊆ A ×ˢ Ω)
    {Z : P × E → E} (hZ : ContDiffOn ℝ (⊤ : ℕ∞) Z (A ×ˢ Ω))
    {τ : ℝ} (Φ : (P × E) × ℝ → E)
    (hjoint : ContDiffOn ℝ (⊤ : ℕ∞) Φ (U ×ˢ Ioo (-τ) τ))
    (hΦ : ∀ p ∈ U, ∀ t ∈ Ioo (-τ) τ,
      HasDerivAt (fun v => Φ (p, v)) (Z (p.1, Φ (p, t))) t ∧ Φ (p, t) ∈ Ω)
    {p : P × E} (hp : p ∈ U) {t : ℝ} (ht : t ∈ Ioo (-τ) τ) (a : P × E) :
    HasDerivAt (fun v => fderiv ℝ (fun q => Φ (q, v)) p a)
      (fderiv ℝ Z (p.1, Φ (p, t)) (a.1, fderiv ℝ (fun q => Φ (q, t)) p a)) t := by
  let L := fderiv ℝ Φ
  let D := fderiv ℝ L (p, t)
  let i : (P × E) →L[ℝ] ((P × E) × ℝ) := ContinuousLinearMap.inl ℝ (P × E) ℝ
  let e : (P × E) × ℝ := (0, 1)
  let H : ((P × E) × ℝ) → P × E := fun q => (q.1.1, Φ q)
  have hpt := (hU.prod isOpen_Ioo).mem_nhds (show (p, t) ∈ U ×ˢ Ioo (-τ) τ from ⟨hp, ht⟩)
  have hs := hjoint.contDiffAt hpt
  have hd : HasFDerivAt L D (p, t) :=
    ((hs.fderiv_right (m := 1) (by simp)).differentiableAt (by simp)).hasFDerivAt
  have hJ : ∀ q ∈ U, ∀ v ∈ Ioo (-τ) τ,
      fderiv ℝ (fun q => Φ (q, v)) q = (L (q, v)).comp i := by
    intro q hq v hv
    exact (((hjoint.contDiffAt ((hU.prod isOpen_Ioo).mem_nhds ⟨hq, hv⟩)).differentiableAt
      (by simp)).hasFDerivAt.comp q (hasFDerivAt_prodMk_left q v)).fderiv
  have htime : ∀ q ∈ U ×ˢ Ioo (-τ) τ, L q e = Z (H q) := by
    intro q hq
    have h := (((hjoint.contDiffAt ((hU.prod isOpen_Ioo).mem_nhds hq)).differentiableAt
      (by simp)).hasFDerivAt.comp q.2 (hasFDerivAt_prodMk_right q.1 q.2)).hasDerivAt
    exact h.unique (hΦ q.1 hq.1 q.2 hq.2).1
  have heq : (fun q => L q e) =ᶠ[𝓝 (p, t)] (fun q => Z (H q)) := by
    filter_upwards [hpt] with q hq
    exact htime q hq
  have happ := (ContinuousLinearMap.apply ℝ E e).hasFDerivAt.comp (p, t) hd
  have hH : HasFDerivAt H
      (((ContinuousLinearMap.fst ℝ P E).comp (ContinuousLinearMap.fst ℝ (P × E) ℝ)).prod
        (L (p, t))) (p, t) := by
    exact (((ContinuousLinearMap.fst ℝ P E).hasFDerivAt.comp (p, t)
      (ContinuousLinearMap.fst ℝ (P × E) ℝ).hasFDerivAt)).prodMk
        (hs.differentiableAt (by simp)).hasFDerivAt
  have hz := ((hZ.contDiffAt ((hA.prod hΩ).mem_nhds
    (show H (p, t) ∈ A ×ˢ Ω from ⟨(hUA hp).1, (hΦ p hp t ht).2⟩))).differentiableAt
      (by simp)).hasFDerivAt.comp (p, t) hH
  have hD := (happ.congr_of_eventuallyEq heq.symm).unique hz
  have hsym := hs.isSymmSndFDerivAt (by simp)
  have hcurve : HasDerivAt (fun v => L (p, v)) (D e) t :=
    (hd.comp t (hasFDerivAt_prodMk_right p t)).hasDerivAt
  have hdir := hcurve.clm_apply (hasDerivAt_const t (i a))
  have hvalue : D e (i a) = fderiv ℝ Z (p.1, Φ (p, t))
      (a.1, fderiv ℝ (fun q => Φ (q, t)) p a) := by
    rw [hsym e (i a), hJ p hp t ht]
    exact congrArg (fun K => K (i a)) hD
  have hJeq : (fun v => fderiv ℝ (fun q => Φ (q, v)) p a) =ᶠ[𝓝 t]
      (fun v => L (p, v) (i a)) := by
    filter_upwards [isOpen_Ioo.mem_nhds ht] with v hv
    exact congrArg (fun K => K a) (hJ p hp v hv)
  rw [hvalue] at hdir
  simpa only [map_zero, add_zero] using hdir.congr_of_eventuallyEq hJeq

/-- At initial time the parameter variation is zero: the flow
starts from its spatial input independently of the parameter
(BB Lemma 9.48, pp. 441–442). -/
theorem parameterFlow_parameter_derivative_zero {P E : Type*}
    [NormedAddCommGroup P] [NormedSpace ℝ P] [NormedAddCommGroup E] [NormedSpace ℝ E]
    {U : Set (P × E)} (hU : IsOpen U) (Φ : (P × E) × ℝ → E)
    (hinit : ∀ p ∈ U, Φ (p, 0) = p.2) {p : P × E} (hp : p ∈ U) (a : P) :
    fderiv ℝ (fun q => Φ (q, 0)) p (a, 0) = 0 := by
  have heq : (fun q => Φ (q, 0)) =ᶠ[𝓝 p] Prod.snd := by
    filter_upwards [hU.mem_nhds hp] with q hq
    exact hinit q hq
  rw [heq.fderiv_eq, fderiv_snd]
  rfl

end RothschildStein.G4
