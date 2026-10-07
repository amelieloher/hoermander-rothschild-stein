-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H1.LocalDilationIntegrability

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
open Set MeasureTheory
namespace RothschildStein.H1
variable {N : ℕ} (G : HomogeneousGroup N)

/-- Positive scaling preserves compact support, including
for a local kernel that is singular at the origin (BB pp. 265–266). -/
theorem hasCompactSupport_scaledFundamentalKernel
    {Γ : (Fin N → ℝ) → ℝ} (hs : HasCompactSupport Γ) {s : ℝ} (ht : 0 < s) :
    HasCompactSupport (scaledFundamentalKernel G s Γ) := by
  let e : (Fin N → ℝ) ≃ₜ (Fin N → ℝ) :=
    { toFun := G.dilate s⁻¹
      invFun := G.dilate s
      left_inv := by intro x; rw [G2.dilate_dilate, mul_inv_cancel₀ ht.ne', G2.dilate_one]
      right_inv := G2.dilate_inv_dilate G ht.ne'
      continuous_toFun := (G2.contDiff_dilate G s⁻¹).continuous
      continuous_invFun := (G2.contDiff_dilate G s).continuous }
  exact (hs.comp_homeomorph e).mul_left (f := fun _ => s ^ 2 * (s ^ G.homogeneousDimension)⁻¹)

/-- Positive scaling preserves continuity on the punctured
carrier (BB p. 266). -/
theorem continuousOn_scaledFundamentalKernel
    {Γ : (Fin N → ℝ) → ℝ} (hc : ContinuousOn Γ ({(0 : Fin N → ℝ)}ᶜ))
    {s : ℝ} (ht : 0 < s) :
    ContinuousOn (scaledFundamentalKernel G s Γ) ({(0 : Fin N → ℝ)}ᶜ) := by
  apply continuousOn_const.mul
  apply hc.comp (G2.continuous_dilate G s⁻¹).continuousOn
  intro x hx
  change G.dilate s⁻¹ x ≠ 0
  intro hz
  exact hx ((G2.dilate_bijective G (inv_ne_zero ht.ne')).injective
    (hz.trans (G2.dilate_zero G _).symm))

/-- A compact locally integrable kernel is integrable globally;
no value or regularity at the origin is required (BB p. 266). -/
theorem integrable_of_locallyIntegrable_compact
    {Γ : (Fin N → ℝ) → ℝ} (hΓ : LocallyIntegrable Γ) (hs : HasCompactSupport Γ) :
    Integrable Γ :=
  (integrableOn_iff_integrable_of_support_subset (subset_tsupport Γ)).mp
    (hΓ.integrableOn_isCompact hs)

end RothschildStein.H1
