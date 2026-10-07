-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H3.IntrinsicWordRestriction
public import RothschildStein.H3.CompactQuasiballCutoff
public import RothschildStein.H3.QuasiballDomain

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
open Set TopologicalSpace
open scoped ENNReal
namespace RothschildStein.H3

/-- The actual quasi-ball cutoff bounds the complete local
fixed norm by its global localized norm at every weighted order. -/
theorem quasiball_cutoff_full_holder_norm_le {N m : ℕ}
    (G : HomogeneousGroup N) (ν : G2.HomogeneousNorm G)
    (x₀ : Fin N → ℝ) {t s : ℝ} (hts : t < s)
    (w : Fin m → ℕ+) (X : Fin m → (Fin N → ℝ) → (Fin N → ℝ))
    (d : (Fin N → ℝ) → (Fin N → ℝ) → ℝ≥0∞) (k : ℕ) (α : ℝ)
    (u : (Fin N → ℝ) → ℝ) :
    holderXENorm w X d (quasiballDomain G ν x₀ t) k α u ≤
      holderXENorm w X d ⊤ k α
        (fun x => u x * smoothQuasiballCutoff G ν x₀ t s x) := by
  exact cutoff_plateau_holderX_norm_le w X d (quasiballDomain G ν x₀ t) k α
    u (smoothQuasiballCutoff G ν x₀ t s) (smoothQuasiballCutoff_one G ν x₀ hts)

end RothschildStein.H3
