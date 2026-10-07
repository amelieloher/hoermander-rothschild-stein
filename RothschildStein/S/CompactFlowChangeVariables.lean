-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.S.FlowChangeVariables

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
open Set MeasureTheory
namespace RothschildStein.S
variable {n : ℕ}

/-- If the reverse-time trajectories from the test support
remain in the buffered start set, that support is contained in the forward
flow image (BB Prop 2.22, p. 89). -/
theorem test_support_subset_flow_image
    {Ω U V K : Set (Fin n → ℝ)} (hΩ : IsOpen Ω) (hKU : K ⊆ U) (hVU : V ⊆ U)
    {X : (Fin n → ℝ) → (Fin n → ℝ)}
    (hX : ContDiffOn ℝ (⊤ : ℕ∞) X Ω) {τ : ℝ} (hτ : 0 < τ)
    (Φ : ((Fin n → ℝ) × ℝ) → (Fin n → ℝ))
    (hΦ : ∀ x ∈ U,Φ (x,0) = x ∧ ∀ t ∈ Ioo (-τ) τ,
      HasDerivAt (fun v => Φ (x,v)) (X (Φ (x,t))) t ∧ Φ (x,t) ∈ Ω)
    {t : ℝ} (ht : t ∈ Ioo (-τ) τ)
    (hback : ∀ y ∈ K,Φ (y,-t) ∈ V) : K ⊆ (fun x => Φ (x,t)) '' V := by
  intro y hy
  have hneg : -t ∈ Ioo (-τ) τ := ⟨by linarith [ht.2],by linarith [ht.1]⟩
  refine ⟨Φ (y,-t),hback y hy,?_⟩
  simpa only [neg_neg] using G1.localFlow_inverse hΩ hX hτ Φ hΦ
    (hKU hy) hneg (hVU (hback y hy))

/-- Compact support localizes the proved flow
change-of-variables identity exactly to the test support K, with the
actual inverse-time Jacobian (BB p. 89, equation (2)). -/
theorem integral_flow_pullback_eq_integral_on_support
    {Ω U V K : Set (Fin n → ℝ)} (hΩ : IsOpen Ω) (hU : IsOpen U)
    (hV : IsOpen V) (hVU : V ⊆ U) (hKU : K ⊆ U)
    {X : (Fin n → ℝ) → (Fin n → ℝ)}
    (hX : ContDiffOn ℝ (⊤ : ℕ∞) X Ω) {τ : ℝ} (hτ : 0 < τ)
    (Φ : ((Fin n → ℝ) × ℝ) → (Fin n → ℝ))
    (hjoint : ContDiffOn ℝ (⊤ : ℕ∞) Φ (U ×ˢ Ioo (-τ) τ))
    (hΦ : ∀ x ∈ U,Φ (x,0) = x ∧ ∀ t ∈ Ioo (-τ) τ,
      HasDerivAt (fun v => Φ (x,v)) (X (Φ (x,t))) t ∧ Φ (x,t) ∈ Ω)
    {t : ℝ} (ht : t ∈ Ioo (-τ) τ)
    (hstay : ∀ x ∈ V,Φ (x,t) ∈ U) (hback : ∀ y ∈ K,Φ (y,-t) ∈ V)
    (f φ : (Fin n → ℝ) → ℝ) (hφ : Function.support φ ⊆ K) :
    (∫ x in V,f x * φ (Φ (x,t))) =
      ∫ y in K,|(fderiv ℝ (fun z => Φ (z,-t)) y).det| * f (Φ (y,-t)) * φ y := by
  have hA := isOpen_flow_image hΩ hU hV hVU hX hτ Φ hjoint.continuousOn hΦ ht hstay
  have hKA := test_support_subset_flow_image hΩ hKU hVU hX hτ Φ hΦ ht hback
  refine (integral_flow_pullback_change_variables hΩ hU hV hVU hX hτ Φ hjoint hΦ ht hstay f φ).trans ?_
  apply setIntegral_eq_of_subset_of_forall_sdiff_eq_zero hA.measurableSet hKA
  intro y hy
  have hz : φ y = 0 := by
    by_contra hn
    exact hy.2 (hφ hn)
  rw [hz,mul_zero]

end RothschildStein.S
