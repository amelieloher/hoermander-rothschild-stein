-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H3.ContinuousSublevelDomain
public import RothschildStein.H3.WeakJetNormFacts

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
namespace RothschildStein.H3
open Set MeasureTheory
open scoped ENNReal
variable {n m : ℕ}

/-- Bounds obtained only at sufficiently large radii control every
smaller local weak norm, so the inverse-radius parameter has no small-radius gap. -/
theorem weakWordENorm_uniform_of_large_sublevel_bounds
    (X : Fin m → (Fin n → ℝ) → (Fin n → ℝ)) (I : List (Fin m))
    (ν : (Fin n → ℝ) → ℝ) (hν : Continuous ν)
    (f : (Fin n → ℝ) → ℝ) (p : ℝ≥0∞) (A R₀ : ℝ)
    (hlocal : ∀ R : ℝ, 0 < R → ∃ g : (Fin n → ℝ) → ℝ,
      hasWeakWordDeriv X (continuousSublevelDomain ν hν R) I f g)
    (hb : ∀ R : ℝ, 0 < R → R₀ ≤ R →
      weakWordENorm X (continuousSublevelDomain ν hν R) I p f ≤ ENNReal.ofReal A) :
    ∀ r : ℝ, 0 < r →
      weakWordENorm X (continuousSublevelDomain ν hν r) I p f ≤ ENNReal.ofReal A := by
  intro r hr
  let R := max r (max R₀ 1)
  have hrR : r ≤ R := le_max_left _ _
  have hR₀R : R₀ ≤ R := (le_max_left R₀ 1).trans (le_max_right _ _)
  have hR : 0 < R := hr.trans_le hrR
  obtain ⟨g, hg⟩ := hlocal R hR
  have hs : (continuousSublevelDomain ν hν r : Set (Fin n → ℝ)) ⊆
      continuousSublevelDomain ν hν R := by
    intro x hx
    change ν x < R
    change ν x < r at hx
    exact hx.trans_le hrR
  exact (weakWordENorm_mono_domain X _ _ hs I p f g hg).trans (hb R hR hR₀R)

end RothschildStein.H3
