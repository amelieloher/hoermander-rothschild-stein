-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.G1.TransportDistance

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set
open scoped ENNReal

namespace RothschildStein.L1

/-- Linear projection of lifted fields transports actual
absolutely continuous controlled curves, with the same measurable controls
and control radius (BB pp. 516–518, Proposition 10.39). -/
theorem isControlledCurve_linear_projection {m n N : ℕ}
    {Ω : Set (Fin n → ℝ)} {U : Set (Fin N → ℝ)} (hU : IsOpen U)
    (P : (Fin N → ℝ) →L[ℝ] (Fin n → ℝ)) (hmap : MapsTo P U Ω)
    (w : Fin m → ℕ+)
    (X : Fin m → (Fin n → ℝ) → (Fin n → ℝ))
    (Z : Fin m → (Fin N → ℝ) → (Fin N → ℝ))
    (hfields : ∀ ξ ∈ U, ∀ i, P (Z i ξ) = X i (P ξ))
    {δ : ℝ} {γ : ℝ → (Fin N → ℝ)} (hγ : isControlledCurve U w Z δ γ) :
    isControlledCurve Ω w X δ (P ∘ γ) := by
  apply G1.isControlledCurve_transport hU P.contDiff.contDiffOn hmap _ hγ
  intro ξ hξ i
  simpa only [ContinuousLinearMap.fderiv] using hfields ξ hξ i

end RothschildStein.L1
