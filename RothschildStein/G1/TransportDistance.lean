-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.G1.ControlledTransport

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set
open scoped Topology ENNReal

namespace RothschildStein.G1

/-- Infimizing an actual scaled transport of all controlled curves
bounds the extended distance, including infinite values (BB p. 22). -/
theorem controlDistance_le_scaled_transport {m n k : ℕ} {Ω : Set (Fin n → ℝ)}
    {Ω' : Set (Fin k → ℝ)} {w : Fin m → ℕ+}
    {X : Fin m → (Fin n → ℝ) → (Fin n → ℝ)}
    {Z : Fin m → (Fin k → ℝ) → (Fin k → ℝ)}
    (F : (Fin n → ℝ) → (Fin k → ℝ)) {scale : ℝ} (hscale : 0 < scale)
    (htransport : ∀ δ γ, isControlledCurve Ω w X δ γ →
      isControlledCurve Ω' w Z (scale * δ) (F ∘ γ)) (x y : Fin n → ℝ) :
    controlDistance Ω' w Z (F x) (F y) ≤ ENNReal.ofReal scale * controlDistance Ω w X x y := by
  conv_rhs => rw [controlDistance, sInf_eq_iInf]
  rw [ENNReal.mul_iInf_of_ne (ne_of_gt (ENNReal.ofReal_pos.mpr hscale)) ENNReal.ofReal_ne_top]
  apply le_iInf
  intro r
  rw [ENNReal.mul_iInf_of_ne (ne_of_gt (ENNReal.ofReal_pos.mpr hscale)) ENNReal.ofReal_ne_top]
  apply le_iInf
  rintro ⟨δ, rfl, γ, hγ, hzero, hone⟩
  have hm := controlDistance_le_of_curve (htransport δ γ hγ)
  simpa only [Function.comp_apply, hzero, hone, ENNReal.ofReal_mul hscale.le] using hm

/-- Distance dilation under mutually inverse, scaled C¹ field transports.
Both transport laws are explicit; the inverse law is derived separately from
the diffeomorphism identities (BB Rem 1.40, p. 22). -/
theorem controlDistance_scaled_transport_eq {m n k : ℕ} {Ω : Set (Fin n → ℝ)}
    {Ω' : Set (Fin k → ℝ)} (hΩ : IsOpen Ω) (hΩ' : IsOpen Ω') {w : Fin m → ℕ+}
    {X : Fin m → (Fin n → ℝ) → (Fin n → ℝ)}
    {Z : Fin m → (Fin k → ℝ) → (Fin k → ℝ)}
    {F : (Fin n → ℝ) → (Fin k → ℝ)} {G : (Fin k → ℝ) → (Fin n → ℝ)}
    (hF : ContDiffOn ℝ 1 F Ω) (hG : ContDiffOn ℝ 1 G Ω')
    (hmapF : MapsTo F Ω Ω') (hmapG : MapsTo G Ω' Ω)
    (hinv : ∀ x ∈ Ω, G (F x) = x) {scale : ℝ} (hscale : 0 < scale)
    (hXF : ∀ x ∈ Ω, ∀ i, fderiv ℝ F x (X i x) = scale ^ (w i : ℕ) • Z i (F x))
    (hZG : ∀ y ∈ Ω', ∀ i, fderiv ℝ G y (Z i y) = scale⁻¹ ^ (w i : ℕ) • X i (G y))
    {x y : Fin n → ℝ} (hx : x ∈ Ω) (hy : y ∈ Ω) :
    controlDistance Ω' w Z (F x) (F y) = ENNReal.ofReal scale * controlDistance Ω w X x y := by
  apply le_antisymm
  · exact controlDistance_le_scaled_transport F hscale
      (fun δ γ hγ => isControlledCurve_transport_scaled hΩ hF hmapF hscale hXF hγ) x y
  · have hback := controlDistance_le_scaled_transport G (inv_pos.mpr hscale)
      (fun δ γ hγ => isControlledCurve_transport_scaled hΩ' hG hmapG (inv_pos.mpr hscale) hZG hγ) (F x) (F y)
    rw [hinv x hx, hinv y hy] at hback
    have hh : ENNReal.ofReal scale * controlDistance Ω w X x y ≤
        ENNReal.ofReal scale * (ENNReal.ofReal scale⁻¹ * controlDistance Ω' w Z (F x) (F y)) := by
      gcongr
    rw [← mul_assoc, ← ENNReal.ofReal_mul hscale.le,
      mul_inv_cancel₀ (ne_of_gt hscale), ENNReal.ofReal_one, one_mul] at hh
    exact hh

/-- Unscaled mutually inverse C¹ field transports preserve distance
(BB Rem 1.40, p. 22). -/
theorem controlDistance_transport_eq {m n k : ℕ} {Ω : Set (Fin n → ℝ)}
    {Ω' : Set (Fin k → ℝ)} (hΩ : IsOpen Ω) (hΩ' : IsOpen Ω') {w : Fin m → ℕ+}
    {X : Fin m → (Fin n → ℝ) → (Fin n → ℝ)} {Z : Fin m → (Fin k → ℝ) → (Fin k → ℝ)}
    {F : (Fin n → ℝ) → (Fin k → ℝ)} {G : (Fin k → ℝ) → (Fin n → ℝ)}
    (hF : ContDiffOn ℝ 1 F Ω) (hG : ContDiffOn ℝ 1 G Ω')
    (hmapF : MapsTo F Ω Ω') (hmapG : MapsTo G Ω' Ω)
    (hinv : ∀ x ∈ Ω, G (F x) = x)
    (hXF : ∀ x ∈ Ω, ∀ i, fderiv ℝ F x (X i x) = Z i (F x))
    (hZG : ∀ y ∈ Ω', ∀ i, fderiv ℝ G y (Z i y) = X i (G y))
    {x y : Fin n → ℝ} (hx : x ∈ Ω) (hy : y ∈ Ω) :
    controlDistance Ω' w Z (F x) (F y) = controlDistance Ω w X x y := by
  simpa only [ENNReal.ofReal_one, one_mul] using controlDistance_scaled_transport_eq hΩ hΩ'
    hF hG hmapF hmapG hinv (scale := 1) zero_lt_one
    (by simpa only [one_pow, one_smul] using hXF)
    (by simpa only [inv_one, one_pow, one_smul] using hZG) hx hy

end RothschildStein.G1
