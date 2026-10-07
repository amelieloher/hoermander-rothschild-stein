-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.G4.ActualFrameInverseColumns

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Filter
open scoped Topology

namespace RothschildStein.G4

/-- Every actual local inverse has the signed endpoint-frame
coordinate derivative bound. The inverse identity near the endpoint is
differentiated to obtain the actual derivative equation; the weighted
inverse-column estimate then applies (BB Lemma 9.51, pp. 446–447). -/
theorem local_inverse_frame_derivative_bound {ι : Type*} {n : ℕ}
    (Z : ι → (Fin n → ℝ) → (Fin n → ℝ)) (w : ι → ℕ+) (B : Fin n → ι)
    (F Ψ : (Fin n → ℝ) → (Fin n → ℝ)) {u y : Fin n → ℝ}
    (hpoint : Ψ y = u) (hF : DifferentiableAt ℝ F u) (hΨ : DifferentiableAt ℝ Ψ y)
    (hright : (fun z => F (Ψ z)) =ᶠ[𝓝 y] (fun z => z))
    (hdet : frameDet Z B y ≠ 0) {r κ : ℝ} (hr : 0 < r) (hκ : 0 ≤ κ)
    (hsmall : (n : ℝ) * κ ≤ 1 / 4)
    (herror : ∀ i j, |frameCoefficient Z B
      (fun z => fderiv ℝ F u (Pi.single j 1) - Z (B j) z) i y| ≤
        κ * r ^ (((w (B i) : ℕ) : ℤ) - ((w (B j) : ℕ) : ℤ))) :
    ∀ (ℓ i : Fin n), |(fderiv ℝ Ψ y (Z (B ℓ) y)) i| ≤ (4 / 3 : ℝ) *
      r ^ (((w (B i) : ℕ) : ℤ) - ((w (B ℓ) : ℕ) : ℤ)) := by
  have hFu : DifferentiableAt ℝ F (Ψ y) := hpoint.symm ▸ hF
  have hchain := hFu.hasFDerivAt.comp y hΨ.hasFDerivAt
  have hid := (hchain.congr_of_eventuallyEq hright.symm).unique (hasFDerivAt_id y)
  rw [hpoint] at hid
  intro ℓ i
  apply actual_frame_inverse_column_bound Z w B (fderiv ℝ F u) hdet hr hκ hsmall herror
    (fderiv ℝ Ψ y (Z (B ℓ) y)) ℓ ?_ i
  have hh := congrArg (fun L : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ) => L (Z (B ℓ) y)) hid
  simpa only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply] using hh

end RothschildStein.G4
