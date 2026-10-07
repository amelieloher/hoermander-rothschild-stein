-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H3.WeakHorizontalRestriction
public import RothschildStein.H3.QuasiballDomainRestriction

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
namespace RothschildStein.H3
open Set MeasureTheory
open scoped ENNReal

/-- The half-radius horizontal weak norm has the exact Phi
lower bound; no continuity of weak norm representatives is assumed. -/
theorem phi_horizontalWeak_half_radius_le {n q : ℕ} (G : HomogeneousGroup n)
    (ν : G2.HomogeneousNorm G) (X : Fin (q+1) → (Fin n → ℝ) → (Fin n → ℝ))
    (x₀ : Fin n → ℝ) {r : ℝ} (hr : 0 < r) (p : ℝ≥0∞) (u : (Fin n → ℝ) → ℝ)
    (hu : memSobolevX driftWeight X (quasiballDomain G ν x₀ r) 2 p u) :
    ENNReal.ofReal ((r/2) *
      (horizontalWeakENorm X (quasiballDomain G ν x₀ (r/2)) p u).toReal) ≤
      phi (Ioo (1/2 : ℝ) 1) r 1
        (fun σ => (horizontalWeakENorm X (quasiballDomain G ν x₀ (σ*r)) p u).toReal) := by
  have hb := phi_half_radius_le
    (N := fun σ => (horizontalWeakENorm X (quasiballDomain G ν x₀ (σ*r)) p u).toReal)
    (L := (horizontalWeakENorm X (quasiballDomain G ν x₀ (r/2)) p u).toReal) 1 hr ENNReal.toReal_nonneg (fun σ hσ => ?_)
  · simpa only [pow_one] using hb
  · have hs := memSobolevX_quasiball_restrict G ν x₀ (by nlinarith [hσ.2] : σ*r ≤ r)
      driftWeight X 2 p u hu
    exact ENNReal.toReal_mono (horizontalWeakENorm_lt_top X _ p u hs).ne
      (horizontalWeakENorm_mono_domain X _ _
        (quasiballDomain_subset_of_le G ν x₀ (by nlinarith [hσ.1] : r/2 ≤ σ*r)) p u hs)

end RothschildStein.H3
