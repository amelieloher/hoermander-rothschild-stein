-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H3.RealSecondNorm
public import RothschildStein.H3.WeakDriftOperatorRestriction
public import RothschildStein.H3.QuasiballDomainRestriction

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public section
noncomputable section
namespace RothschildStein.H3
open Set MeasureTheory
open scoped ENNReal

/-- The actual real quasiball second-norm step specializes to the
midpoint radii, with the source controlled by the full-ball operator norm. -/
theorem quasiball_second_midpoint_with_constants {n q : ℕ}
    (G : HomogeneousGroup n) (ν : G2.HomogeneousNorm G)
    (X : Fin (q+1) → (Fin n → ℝ) → (Fin n → ℝ))
    (p : ℝ≥0∞) {C a b : ℝ} (hC : 0 ≤ C)
    (hstep : ∀ x₀ : Fin n → ℝ, ∀ t s : ℝ, 0 < t → t < s → s/2 ≤ t →
      ∀ u : (Fin n → ℝ) → ℝ,
        memSobolevX driftWeight X (quasiballDomain G ν x₀ s) 2 p u →
      ∀ D : WeakDriftOperatorData X (quasiballDomain G ν x₀ s) p u,
      (driftSecondWeakENorm X (quasiballDomain G ν x₀ t) p u).toReal ≤
        C * ((eLpNorm D.operator p (volume.restrict (G2.gaugeBall G ν x₀ s))).toReal +
          b/(s-t)^2 * (eLpNorm u p (volume.restrict (G2.gaugeBall G ν x₀ s))).toReal +
          2*a/(s-t) * (horizontalWeakENorm X (quasiballDomain G ν x₀ s) p u).toReal))
    (x₀ : Fin n → ℝ) {r : ℝ} (hr : 0 < r)
    (u : (Fin n → ℝ) → ℝ)
    (hu : memSobolevX driftWeight X (quasiballDomain G ν x₀ r) 2 p u)
    (D : WeakDriftOperatorData X (quasiballDomain G ν x₀ r) p u) :
    ∀ σ ∈ Ioo (1/2 : ℝ) 1,
      (driftSecondWeakENorm X (quasiballDomain G ν x₀ (σ*r)) p u).toReal ≤
        C * ((eLpNorm D.operator p (volume.restrict (G2.gaugeBall G ν x₀ r))).toReal +
          b/(((1-σ)*r)/2)^2 *
            (eLpNorm u p (volume.restrict (G2.gaugeBall G ν x₀ (((1+σ)/2)*r)))).toReal +
          2*a/(((1-σ)*r)/2) *
            (horizontalWeakENorm X (quasiballDomain G ν x₀ (((1+σ)/2)*r)) p u).toReal) := by
  intro σ hσ
  have hsle : ((1+σ)/2)*r ≤ r := by nlinarith [hσ.2]
  have hsub := quasiballDomain_subset_of_le G ν x₀ hsle
  have hs := memSobolevX_quasiball_restrict G ν x₀ hsle driftWeight X 2 p u hu
  let E := D.restrict (quasiballDomain G ν x₀ (((1+σ)/2)*r)) hsub
  have hb := hstep x₀ (σ*r) (((1+σ)/2)*r)
    (by nlinarith [hσ.1]) (by nlinarith [hσ.2]) (by nlinarith [hσ.1]) u hs E
  have hgap : ((1+σ)/2)*r - σ*r = ((1-σ)*r)/2 := by ring
  rw [hgap] at hb
  have hf : (eLpNorm E.operator p
      (volume.restrict (G2.gaugeBall G ν x₀ (((1+σ)/2)*r)))).toReal ≤
      (eLpNorm D.operator p (volume.restrict (G2.gaugeBall G ν x₀ r))).toReal :=
    D.restrict_operator_realNorm_le _ hsub
  exact hb.trans (mul_le_mul_of_nonneg_left
    (add_le_add (add_le_add hf le_rfl) le_rfl) hC)

end RothschildStein.H3
