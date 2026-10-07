-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module
public import RothschildStein.L1.CanonicalFrameMap
@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set
namespace RothschildStein.L1

/-- The open coefficient/base domain of a time-rescaled frame map. -/
def canonicalFrameDomain {N : ℕ} (a : ℝ)
    (U : Set ((Fin N → ℝ) × (Fin N → ℝ))) :
    Set ((Fin N → ℝ) × (Fin N → ℝ)) :=
  (fun q => (a⁻¹ • q.2,q.1)) ⁻¹' U

/-- The canonical map has an actual open domain. -/
theorem canonicalFrameDomain_isOpen {N : ℕ} (a : ℝ)
    {U : Set ((Fin N → ℝ) × (Fin N → ℝ))} (hU : IsOpen U) :
    IsOpen (canonicalFrameDomain a U) :=
  hU.preimage ((continuous_snd.const_smul a⁻¹).prodMk continuous_fst)

/-- Joint smoothness holds on the entire canonical domain inherited
from the actual flow cylinder. -/
theorem canonicalFrameMap_contDiffOn {N : ℕ} (a : ℝ) {τ : ℝ}
    (ha : a ∈ Ioo (-τ) τ)
    {U : Set ((Fin N → ℝ) × (Fin N → ℝ))}
    (Φ : (((Fin N → ℝ) × (Fin N → ℝ)) × ℝ) → (Fin N → ℝ))
    (hΦ : ContDiffOn ℝ (⊤ : ℕ∞) Φ (U ×ˢ Ioo (-τ) τ)) :
    ContDiffOn ℝ (⊤ : ℕ∞) (canonicalFrameMap a Φ) (canonicalFrameDomain a U) := by
  have hc : ContDiff ℝ (⊤ : ℕ∞)
      (fun q : (Fin N → ℝ) × (Fin N → ℝ) => ((a⁻¹ • q.2,q.1),a)) :=
    ((contDiff_snd.const_smul a⁻¹).prodMk contDiff_fst).prodMk contDiff_const
  exact hΦ.comp hc.contDiffOn (fun _ hq => ⟨hq,ha⟩)
end RothschildStein.L1
