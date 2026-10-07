-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.S.FlowChartGeometry
public import Mathlib.MeasureTheory.Function.Jacobian

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public section
noncomputable section
open Set MeasureTheory
namespace RothschildStein.S
variable {n : ℕ}

/-- The actual inverse-time flow gives the pullback
change-of-variables identity on the buffered open chart. The proof uses
Mathlib's determinant formula and G1's inverse identity, not an assumed
integration identity (BB Prop 2.22, p. 89). -/
theorem integral_flow_pullback_change_variables
    {Ω U V : Set (Fin n → ℝ)} (hΩ : IsOpen Ω) (hU : IsOpen U)
    (hV : IsOpen V) (hVU : V ⊆ U)
    {X : (Fin n → ℝ) → (Fin n → ℝ)}
    (hX : ContDiffOn ℝ (⊤ : ℕ∞) X Ω) {τ : ℝ} (hτ : 0 < τ)
    (Φ : ((Fin n → ℝ) × ℝ) → (Fin n → ℝ))
    (hjoint : ContDiffOn ℝ (⊤ : ℕ∞) Φ (U ×ˢ Ioo (-τ) τ))
    (hΦ : ∀ x ∈ U,Φ (x,0) = x ∧ ∀ t ∈ Ioo (-τ) τ,
      HasDerivAt (fun v => Φ (x,v)) (X (Φ (x,t))) t ∧ Φ (x,t) ∈ Ω)
    {t : ℝ} (ht : t ∈ Ioo (-τ) τ)
    (hstay : ∀ x ∈ V,Φ (x,t) ∈ U)
    (f φ : (Fin n → ℝ) → ℝ) :
    (∫ x in V,f x * φ (Φ (x,t))) =
      ∫ y in (fun x => Φ (x,t)) '' V,
        |(fderiv ℝ (fun z => Φ (z,-t)) y).det| * f (Φ (y,-t)) * φ y := by
  let A := (fun x => Φ (x,t)) '' V
  have hA : IsOpen A := isOpen_flow_image hΩ hU hV hVU hX hτ Φ hjoint.continuousOn hΦ ht hstay
  have hAU : A ⊆ U := by rintro _ ⟨x,hx,rfl⟩; exact hstay x hx
  have hneg : -t ∈ Ioo (-τ) τ := ⟨by linarith [ht.2],by linarith [ht.1]⟩
  have hinv : ∀ x ∈ V,Φ (Φ (x,t),-t) = x :=
    fun x hx => G1.localFlow_inverse hΩ hX hτ Φ hΦ (hVU hx) ht (hstay x hx)
  have hstayInv : ∀ y ∈ A,Φ (y,-t) ∈ U := by
    rintro _ ⟨x,hx,rfl⟩
    rw [hinv x hx]
    exact hVU hx
  have hInj := flow_time_injOn hΩ hAU hX hτ Φ hΦ hneg hstayInv
  have hImage : (fun y => Φ (y,-t)) '' A = V := by
    ext x
    constructor
    · rintro ⟨y,⟨z,hz,rfl⟩,rfl⟩
      simpa only [hinv z hz] using hz
    · intro hx
      exact ⟨Φ (x,t),⟨x,hx,rfl⟩,hinv x hx⟩
  have hD : ∀ y ∈ A,HasFDerivWithinAt (fun z => Φ (z,-t))
      (fderiv ℝ (fun z => Φ (z,-t)) y) A y := by
    intro y hy
    have hs := (hjoint.contDiffAt ((hU.prod isOpen_Ioo).mem_nhds ⟨hAU hy,hneg⟩)).comp y
      (contDiffAt_id.prodMk contDiffAt_const)
    exact (hs.differentiableAt (by simp)).hasFDerivAt.hasFDerivWithinAt
  have H := integral_image_eq_integral_abs_det_fderiv_smul volume hA.measurableSet hD hInj
    (fun x => f x * φ (Φ (x,t)))
  rw [hImage] at H
  refine H.trans (setIntegral_congr_fun hA.measurableSet ?_)
  intro y hy
  have he := G1.localFlow_inverse hΩ hX hτ Φ hΦ (hAU hy) hneg (hstayInv y hy)
  simp only [neg_neg] at he
  simp only [smul_eq_mul,he,mul_assoc]

end RothschildStein.S
