-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Moser.MeanValueParabolicTests
public import HeatKernel.Moser.StationaryTests
public import HeatKernel.Moser.MeanValueSectionDerivatives
import Mathlib.Tactic

/-! # Time and horizontal derivatives of transported parabolic tests -/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set MeasureTheory RothschildStein RothschildStein.G2
namespace HeatKernel

/-- The time derivative of a transported test has the inverse quadratic scale. -/
theorem fderiv_parabolicTestTransport_time {N : ℕ} (G : HomogeneousGroup N)
    (t₀ : ℝ) (x₀ : Fin N → ℝ) (r : ℝ) (hr : 0 < r)
    {φ : ℝ × (Fin N → ℝ) → ℝ} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (t : ℝ) (x : Fin N → ℝ) :
    fderiv ℝ (parabolicTestTransport G t₀ x₀ r hr φ) (t, x) (1, 0) =
      (r ^ 2)⁻¹ * fderiv ℝ φ
        ((r ^ 2)⁻¹ * (-t₀ + t), G.dilate r⁻¹ (G.mul (G.inv x₀) x)) (1, 0) := by
  let y := G.dilate r⁻¹ (G.mul (G.inv x₀) x)
  let s := (r ^ 2)⁻¹ * (-t₀ + t)
  have hd := hφ.differentiable (by simp)
  have hψ : Differentiable ℝ (fun s : ℝ => φ (s, y)) :=
    hd.comp (differentiable_id.prodMk (differentiable_const y))
  have hl : HasDerivAt (fun s : ℝ => (r ^ 2)⁻¹ * (-t₀ + s)) (r ^ 2)⁻¹ t := by
    simpa using ((hasDerivAt_id t).const_add (-t₀)).const_mul ((r ^ 2)⁻¹)
  have hc := (hψ s).hasDerivAt.comp t hl
  rw [← deriv_timeSection_eq_fderiv
    ((contDiff_parabolicTestTransport G t₀ x₀ r hr hφ).differentiable (by simp))]
  change deriv ((fun s : ℝ => φ (s, y)) ∘ (fun z : ℝ => (r ^ 2)⁻¹ * (-t₀ + z))) t = _
  rw [hc.deriv, deriv_timeSection_eq_fderiv hd s y]
  ring

/-- Each horizontal derivative of a transported test has the inverse spatial scale. -/
theorem fderiv_parabolicTestTransport_horizontal {N q : ℕ} (G : HomogeneousGroup N)
    (hq : q ≤ N) (hw : ∀ i : Fin q, G.weight (Fin.castLE hq i) = 1)
    (t₀ : ℝ) (x₀ : Fin N → ℝ) (r : ℝ) (hr : 0 < r)
    {φ : ℝ × (Fin N → ℝ) → ℝ} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (i : Fin q) (t : ℝ) (x : Fin N → ℝ) :
    fderiv ℝ (parabolicTestTransport G t₀ x₀ r hr φ) (t, x)
      (0, G.horizontalFields hq i x) =
      r⁻¹ * fderiv ℝ φ
        ((r ^ 2)⁻¹ * (-t₀ + t), G.dilate r⁻¹ (G.mul (G.inv x₀) x))
          (0, G.horizontalFields hq i (G.dilate r⁻¹ (G.mul (G.inv x₀) x))) := by
  let s := (r ^ 2)⁻¹ * (-t₀ + t)
  let ψ := fun y : Fin N → ℝ => φ (s, y)
  have hψ : ContDiff ℝ (⊤ : ℕ∞) ψ :=
    hφ.comp (contDiff_const.prodMk contDiff_id)
  have htest := (contDiff_parabolicTestTransport G t₀ x₀ r hr hφ).differentiable (by simp)
  rw [← fderiv_spatial_section_apply (htest (t, x))]
  change fieldDerivative (G.horizontalFields hq i)
    (translatedDilatedFunction G x₀ r ψ) x = _
  rw [fieldDerivative_translatedDilatedFunction G hq hw x₀ hr hψ]
  change r⁻¹ * fderiv ℝ ψ (G.dilate r⁻¹ (G.mul (G.inv x₀) x))
    (G.horizontalFields hq i (G.dilate r⁻¹ (G.mul (G.inv x₀) x))) = _
  rw [fderiv_spatial_section_apply
    ((hφ.differentiable (by simp)) (s, G.dilate r⁻¹ (G.mul (G.inv x₀) x)))]

end HeatKernel
