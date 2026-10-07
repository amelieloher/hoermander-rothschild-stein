-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H3.HalfRadiusConditional
public import RothschildStein.H3.SobolevSecondNormBound
public import RothschildStein.H3.ScaledSecondNormComparison
public import RothschildStein.H3.QuasiballDomainRestriction

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public section
noncomputable section
namespace RothschildStein.H3
open Set MeasureTheory
open scoped ENNReal

/-- The weighted half-radius estimate implies an estimate for the exact
fixed Sobolev norm, with all radius dependence displayed. -/
theorem fixed_norm_estimate_of_halfRadius {n q : ℕ}
    (G : HomogeneousGroup n) (ν : G2.HomogeneousNorm G)
    (X : Fin (q+1) → (Fin n → ℝ) → (Fin n → ℝ))
    (p : ℝ≥0∞) (A : ℝ) (hest : HalfRadiusEstimate G ν X p A)
    (x₀ : Fin n → ℝ) (r : ℝ) (hr : 0 < r) (u : (Fin n → ℝ) → ℝ)
    (hu : memSobolevX driftWeight X (quasiballDomain G ν x₀ r) 2 p u)
    (D : WeakDriftOperatorData X (quasiballDomain G ν x₀ r) p u) :
    (sobolevXENorm driftWeight X (quasiballDomain G ν x₀ (r/2)) 2 p u).toReal ≤
      ((wordFamily (driftWeight (q := q)) 2).card : ℝ)*(1+r+r^2)*A*
        ((eLpNorm D.operator p (volume.restrict (G2.gaugeBall G ν x₀ r))).toReal+
          r⁻¹^2*(eLpNorm u p (volume.restrict (G2.gaugeBall G ν x₀ r))).toReal) := by
  have hh := memSobolevX_quasiball_restrict G ν x₀ (show r/2 ≤ r by linarith)
    driftWeight X 2 p u hu
  have hb := sobolevXENorm_toReal_le_second_norms X _ p u hh
  have hc := second_norm_sum_le_scaled_sum r
    (eLpNorm u p (volume.restrict (G2.gaugeBall G ν x₀ (r/2)))).toReal
    (horizontalWeakENorm X (quasiballDomain G ν x₀ (r/2)) p u).toReal
    (driftSecondWeakENorm X (quasiballDomain G ν x₀ (r/2)) p u).toReal
    hr ENNReal.toReal_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg
  have hcard : 0 ≤ ((wordFamily (driftWeight (q := q)) 2).card : ℝ) := Nat.cast_nonneg _
  have hf : 0 ≤ 1+r+r^2 := by positivity
  calc
    _ ≤ ((wordFamily (driftWeight (q := q)) 2).card : ℝ)*
        (1+r+r^2)*
        ((driftSecondWeakENorm X (quasiballDomain G ν x₀ (r/2)) p u).toReal+
          r⁻¹*(horizontalWeakENorm X (quasiballDomain G ν x₀ (r/2)) p u).toReal+
          r⁻¹^2*(eLpNorm u p (volume.restrict (G2.gaugeBall G ν x₀ (r/2)))).toReal) := by
      exact hb.trans (by simpa only [quasiballDomain, TopologicalSpace.Opens.coe_mk, mul_assoc] using mul_le_mul_of_nonneg_left hc hcard)
    _ ≤ _ := by
      simpa only [mul_assoc] using
        mul_le_mul_of_nonneg_left (hest x₀ r hr u hu D) (mul_nonneg hcard hf)

end RothschildStein.H3
