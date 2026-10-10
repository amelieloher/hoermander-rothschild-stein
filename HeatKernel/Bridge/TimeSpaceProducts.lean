-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import Mathlib

/-! # Support and differentials of separated time-space test functions -/

@[expose] public section
open Set
namespace HeatKernel

/-- The support of a separated product lies in the product of the two supports. -/
theorem tsupport_time_space_product_subset {α β : Type*}
    [TopologicalSpace α] [TopologicalSpace β] (ψ : α → ℝ) (φ : β → ℝ) :
    tsupport (fun z : α × β => ψ z.1 * φ z.2) ⊆ tsupport ψ ×ˢ tsupport φ := by
  apply closure_minimal _ ((isClosed_tsupport ψ).prod (isClosed_tsupport φ))
  intro z hz
  exact ⟨subset_tsupport ψ (mul_ne_zero_iff.mp hz).1,
    subset_tsupport φ (mul_ne_zero_iff.mp hz).2⟩

/-- Two compactly supported factors give a compactly supported space-time product. -/
theorem hasCompactSupport_time_space_product {α β : Type*}
    [TopologicalSpace α] [TopologicalSpace β] {ψ : α → ℝ} {φ : β → ℝ}
    (hψ : HasCompactSupport ψ) (hφ : HasCompactSupport φ) :
    HasCompactSupport (fun z : α × β => ψ z.1 * φ z.2) :=
  (hψ.prod hφ).of_isClosed_subset (isClosed_tsupport _)
    (tsupport_time_space_product_subset ψ φ)

/-- The differential of a separated product splits into its two directions. -/
theorem fderiv_time_space_product_apply {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {ψ : ℝ → ℝ} {φ : E → ℝ} {t : ℝ} {x : E}
    (hψ : DifferentiableAt ℝ ψ t) (hφ : DifferentiableAt ℝ φ x) (b : ℝ) (v : E) :
    fderiv ℝ (fun z : ℝ × E => ψ z.1 * φ z.2) (t, x) (b, v) =
      ψ t * fderiv ℝ φ x v + φ x * (deriv ψ t * b) := by
  rw [fderiv_fun_mul (hψ.comp (t, x) differentiableAt_fst)
    (hφ.comp (t, x) differentiableAt_snd)]
  have hp := fderiv_comp (t, x) hψ (differentiableAt_fst (𝕜 := ℝ) (p := (t, x)))
  have hq := fderiv_comp (t, x) hφ (differentiableAt_snd (𝕜 := ℝ) (p := (t, x)))
  change fderiv ℝ (fun z : ℝ × E => ψ z.1) (t, x) = _ at hp
  change fderiv ℝ (fun z : ℝ × E => φ z.2) (t, x) = _ at hq
  rw [hp, hq]
  simp only [add_apply, smul_apply,
    ContinuousLinearMap.comp_apply, fderiv_fst, fderiv_snd,
    ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd', smul_eq_mul,
    fderiv_eq_deriv_mul]

/-- The temporal differential differentiates only the temporal factor. -/
theorem fderiv_time_space_product_time {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {ψ : ℝ → ℝ} {φ : E → ℝ} {t : ℝ} {x : E}
    (hψ : DifferentiableAt ℝ ψ t) (hφ : DifferentiableAt ℝ φ x) :
    fderiv ℝ (fun z : ℝ × E => ψ z.1 * φ z.2) (t, x) (1, 0) = deriv ψ t * φ x := by
  simpa [mul_comm] using fderiv_time_space_product_apply hψ hφ 1 0

/-- A spatial differential differentiates only the spatial factor. -/
theorem fderiv_time_space_product_space {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {ψ : ℝ → ℝ} {φ : E → ℝ} {t : ℝ} {x : E}
    (hψ : DifferentiableAt ℝ ψ t) (hφ : DifferentiableAt ℝ φ x) (v : E) :
    fderiv ℝ (fun z : ℝ × E => ψ z.1 * φ z.2) (t, x) (0, v) = ψ t * fderiv ℝ φ x v := by
  simpa using fderiv_time_space_product_apply hψ hφ 0 v

end HeatKernel
