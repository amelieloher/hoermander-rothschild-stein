-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.G4.FlowVariationIntegral
public import RothschildStein.G4.LinearFieldDirectional
public import RothschildStein.G4.ParameterVariation

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set MeasureTheory
open scoped BigOperators

namespace RothschildStein.G4

/-- Smooth fields have a jointly smooth parameter-linear family
(BB Lemma 9.48, pp. 441–442). -/
theorem linear_field_family_contDiffOn {m n : ℕ} {Ω : Set (Fin n → ℝ)}
    (W : Fin m → (Fin n → ℝ) → (Fin n → ℝ))
    (hW : ∀ j, ContDiffOn ℝ (⊤ : ℕ∞) (W j) Ω) (A : Set (Fin m → ℝ)) :
    ContDiffOn ℝ (⊤ : ℕ∞) (fun p : (Fin m → ℝ) × (Fin n → ℝ) => ∑ j, p.1 j • W j p.2) (A ×ˢ Ω) := by
  apply ContDiffOn.sum
  intro j _
  have hf : ContDiff ℝ (⊤ : ℕ∞) (fun p : (Fin m → ℝ) × (Fin n → ℝ) => p.1) := contDiff_fst
  have hc : ContDiff ℝ (⊤ : ℕ∞) (fun p : (Fin m → ℝ) × (Fin n → ℝ) => p.1 j) := by
    simpa only [Function.comp_def, ContinuousLinearMap.proj_apply] using
      (ContinuousLinearMap.proj j : (Fin m → ℝ) →L[ℝ] ℝ).contDiff.comp hf
  exact hc.contDiffOn.smul ((hW j).comp contDiffOn_snd (fun p hp => hp.2))

/-- Fixed linear combinations preserve field smoothness
(BB Lemma 9.48, pp. 441–442). -/
theorem linear_field_combination_contDiffOn {m n : ℕ} {Ω : Set (Fin n → ℝ)}
    (W : Fin m → (Fin n → ℝ) → (Fin n → ℝ))
    (hW : ∀ j, ContDiffOn ℝ (⊤ : ℕ∞) (W j) Ω) (z : Fin m → ℝ) :
    ContDiffOn ℝ (⊤ : ℕ∞) (fun y => ∑ j, z j • W j y) Ω := by
  apply ContDiffOn.sum
  intro j _
  exact (hW j).const_smul (z j)

/-- The actual derivative in coefficient z_i of the exponential
flow of Σ z_j W_j is the actual transported W_i integral. Joint smoothness
holds under joint smoothness of the parameter flow; the finite trajectory buffer is explicit
(BB Lemma 9.48, pp. 441–442). -/
theorem linear_field_flow_parameter_integral_of_joint_contDiff {m n : ℕ}
    {A : Set (Fin m → ℝ)} {Ω U : Set (Fin n → ℝ)}
    (hA : IsOpen A) (hΩ : IsOpen Ω) (hU : IsOpen U) (hUΩ : U ⊆ Ω)
    (W : Fin m → (Fin n → ℝ) → (Fin n → ℝ))
    (hW : ∀ j, ContDiffOn ℝ (⊤ : ℕ∞) (W j) Ω)
    {τ : ℝ} (hτ : 0 < τ) (Φ : (((Fin m → ℝ) × (Fin n → ℝ)) × ℝ) → (Fin n → ℝ))
    (hjoint : ContDiffOn ℝ (⊤ : ℕ∞) Φ ((A ×ˢ U) ×ˢ Ioo (-τ) τ))
    (hΦ : ∀ p ∈ A ×ˢ U, Φ (p, 0) = p.2 ∧ ∀ s ∈ Ioo (-τ) τ,
      HasDerivAt (fun v => Φ (p, v)) (∑ j, p.1 j • W j (Φ (p, s))) s ∧ Φ (p, s) ∈ Ω)
    {z : Fin m → ℝ} (hz : z ∈ A) {x : Fin n → ℝ} (hx : x ∈ U)
    {t : ℝ} (ht : t ∈ Ioo (-τ) τ)
    (hend : ∀ s ∈ uIcc 0 t, Φ ((z, x), s) ∈ U) (i : Fin m) :
    fderiv ℝ (fun p => Φ (p, t)) (z, x) (Pi.single i 1, 0) = ∫ s in 0..t,
      fderiv ℝ (fun y => Φ ((z, y), t - s)) (Φ ((z, x), s)) (W i (Φ ((z, x), s))) := by
  classical
  let Z : ((Fin m → ℝ) × (Fin n → ℝ)) → Fin n → ℝ := fun p => ∑ j, p.1 j • W j p.2
  let Wz : (Fin n → ℝ) → Fin n → ℝ := fun y => ∑ j, z j • W j y
  let θ : ((Fin n → ℝ) × ℝ) → Fin n → ℝ := fun q => Φ ((z, q.1), q.2)
  let Y : ℝ → Fin n → ℝ := fun s => fderiv ℝ (fun p => Φ (p, s)) (z, x) (Pi.single i 1, 0)
  let F : ℝ → Fin n → ℝ := fun s => W i (θ (x, s))
  have hZ : ContDiffOn ℝ (⊤ : ℕ∞) Z (A ×ˢ Ω) := linear_field_family_contDiffOn W hW A
  have hWz : ContDiffOn ℝ (⊤ : ℕ∞) Wz Ω := linear_field_combination_contDiffOn W hW z
  have hθ : ContDiffOn ℝ (⊤ : ℕ∞) θ (U ×ˢ Ioo (-τ) τ) :=
    hjoint.comp ((contDiffOn_const.prodMk contDiffOn_fst).prodMk contDiffOn_snd)
      (fun q hq => ⟨⟨hz, hq.1⟩, hq.2⟩)
  have hθsol : ∀ y ∈ U, θ (y, 0) = y ∧ ∀ s ∈ Ioo (-τ) τ,
      HasDerivAt (fun v => θ (y, v)) (Wz (θ (y, s))) s ∧ θ (y, s) ∈ Ω :=
    fun y hy => hΦ (z, y) ⟨hz, hy⟩
  have ht₀ : (0 : ℝ) ∈ Ioo (-τ) τ := ⟨by linarith, hτ⟩
  have hsub : uIcc 0 t ⊆ Ioo (-τ) τ := ordConnected_Ioo.uIcc_subset ht₀ ht
  have hv : ∀ s ∈ uIcc 0 t, HasDerivAt Y (fderiv ℝ Wz (θ (x, s)) (Y s) + F s) s := by
    intro s hs
    have hD := parameterFlow_variational_of_joint_contDiff hA hΩ (hA.prod hU)
      (fun p hp => ⟨hp.1, hUΩ hp.2⟩) hZ Φ hjoint (fun p hp => (hΦ p hp).2)
      (show (z, x) ∈ A ×ˢ U from ⟨hz, hx⟩) (hsub hs) (Pi.single i 1, 0)
    change HasDerivAt Y (fderiv ℝ (fun p : (Fin m → ℝ) × (Fin n → ℝ) => ∑ j, p.1 j • W j p.2)
      (z, θ (x, s)) (Pi.single i 1, Y s)) s at hD
    rw [linear_field_parameter_forcing W z (θ (x, s)) (Y s)
      (fun j => ((hW j).contDiffAt (hΩ.mem_nhds ((hθsol x hx).2 s (hsub hs)).2)).differentiableAt (by simp)) i] at hD
    exact hD
  have hF : ContinuousOn F (uIcc 0 t) := by
    intro s hs
    exact (((hW i).contDiffAt (hΩ.mem_nhds ((hθsol x hx).2 s (hsub hs)).2)).continuousAt.comp
      (f := fun v : ℝ => θ (x, v)) (((hθsol x hx).2 s (hsub hs)).1.continuousAt)).continuousWithinAt
  have hzero : Y 0 = 0 := parameterFlow_parameter_derivative_zero (hA.prod hU) Φ
    (fun p hp => (hΦ p hp).1) (show (z, x) ∈ A ×ˢ U from ⟨hz, hx⟩) (Pi.single i 1)
  exact localFlow_variation_integral_of_joint_contDiff hΩ hU hWz hτ θ hθ hθsol hx ht hend F Y hF hv hzero

/-- The coefficient derivative of the actual continuous linear-field
flow has the transported integral formula, with smooth dependence supplied
under joint smoothness of the parameter flow (BB Lemma 9.48, pp. 441–442). -/
theorem linear_field_flow_parameter_integral {m n : ℕ}
    {A : Set (Fin m → ℝ)} {Ω U : Set (Fin n → ℝ)}
    (hA : IsOpen A) (hΩ : IsOpen Ω) (hU : IsOpen U) (hUΩ : U ⊆ Ω)
    (W : Fin m → (Fin n → ℝ) → (Fin n → ℝ))
    (hW : ∀ j, ContDiffOn ℝ (⊤ : ℕ∞) (W j) Ω)
    {τ : ℝ} (hτ : 0 < τ) (Φ : (((Fin m → ℝ) × (Fin n → ℝ)) × ℝ) → (Fin n → ℝ))
    (hc : ContinuousOn Φ ((A ×ˢ U) ×ˢ Ioo (-τ) τ))
    (hΦ : ∀ p ∈ A ×ˢ U, Φ (p, 0) = p.2 ∧ ∀ s ∈ Ioo (-τ) τ,
      HasDerivAt (fun v => Φ (p, v)) (∑ j, p.1 j • W j (Φ (p, s))) s ∧ Φ (p, s) ∈ Ω)
    {z : Fin m → ℝ} (hz : z ∈ A) {x : Fin n → ℝ} (hx : x ∈ U)
    {t : ℝ} (ht : t ∈ Ioo (-τ) τ)
    (hend : ∀ s ∈ uIcc 0 t, Φ ((z, x), s) ∈ U) (i : Fin m) :
    fderiv ℝ (fun p => Φ (p, t)) (z, x) (Pi.single i 1, 0) = ∫ s in 0..t,
      fderiv ℝ (fun y => Φ ((z, y), t - s)) (Φ ((z, x), s)) (W i (Φ ((z, x), s))) := by
  have hjoint := parameterFlow_contDiffOn hA hΩ (hA.prod hU)
    (fun p hp => ⟨hp.1, hUΩ hp.2⟩) (linear_field_family_contDiffOn W hW A) hτ Φ hc hΦ
  exact linear_field_flow_parameter_integral_of_joint_contDiff hA hΩ hU hUΩ W hW hτ Φ
    hjoint hΦ hz hx ht hend i

/-- The same transported formula for the parameter-only derivative,
with the initial spatial point held fixed (BB Lemma 9.48, pp. 441–442). -/
theorem linear_field_flow_coefficient_integral {m n : ℕ}
    {A : Set (Fin m → ℝ)} {Ω U : Set (Fin n → ℝ)}
    (hA : IsOpen A) (hΩ : IsOpen Ω) (hU : IsOpen U) (hUΩ : U ⊆ Ω)
    (W : Fin m → (Fin n → ℝ) → (Fin n → ℝ))
    (hW : ∀ j, ContDiffOn ℝ (⊤ : ℕ∞) (W j) Ω)
    {τ : ℝ} (hτ : 0 < τ) (Φ : (((Fin m → ℝ) × (Fin n → ℝ)) × ℝ) → (Fin n → ℝ))
    (hc : ContinuousOn Φ ((A ×ˢ U) ×ˢ Ioo (-τ) τ))
    (hΦ : ∀ p ∈ A ×ˢ U, Φ (p, 0) = p.2 ∧ ∀ s ∈ Ioo (-τ) τ,
      HasDerivAt (fun v => Φ (p, v)) (∑ j, p.1 j • W j (Φ (p, s))) s ∧ Φ (p, s) ∈ Ω)
    {z : Fin m → ℝ} (hz : z ∈ A) {x : Fin n → ℝ} (hx : x ∈ U)
    {t : ℝ} (ht : t ∈ Ioo (-τ) τ)
    (hend : ∀ s ∈ uIcc 0 t, Φ ((z, x), s) ∈ U) (i : Fin m) :
    fderiv ℝ (fun z' => Φ ((z', x), t)) z (Pi.single i 1) = ∫ s in 0..t,
      fderiv ℝ (fun y => Φ ((z, y), t - s)) (Φ ((z, x), s)) (W i (Φ ((z, x), s))) := by
  have hjoint := parameterFlow_contDiffOn hA hΩ (hA.prod hU)
    (fun p hp => ⟨hp.1, hUΩ hp.2⟩) (linear_field_family_contDiffOn W hW A) hτ Φ hc hΦ
  have hdiff : DifferentiableAt ℝ (fun p => Φ (p, t)) (z, x) :=
    ((hjoint.contDiffAt (((hA.prod hU).prod isOpen_Ioo).mem_nhds ⟨⟨hz, hx⟩, ht⟩)).comp
      (z, x) (contDiffAt_id.prodMk contDiffAt_const)).differentiableAt (by simp)
  have hslice := (hdiff.hasFDerivAt.comp z (hasFDerivAt_prodMk_left (𝕜 := ℝ) z x)).fderiv
  simp only [Function.comp_def] at hslice
  rw [hslice]
  simpa only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.inl_apply] using
    linear_field_flow_parameter_integral hA hΩ hU hUΩ W hW hτ Φ hc hΦ hz hx ht hend i

end RothschildStein.G4
