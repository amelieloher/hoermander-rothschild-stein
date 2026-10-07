-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H3.QuasiballSecondEstimate
public import RothschildStein.H3.QuasiballSecondMidpoint
public import RothschildStein.H3.SecondPhiBound
public import RothschildStein.H3.QuasiballZeroPhi
public import RothschildStein.H3.WeakHorizontalRestriction

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public section
noncomputable section
namespace RothschildStein.H3
open Set MeasureTheory
open scoped ENNReal

/-- Step 1: the actual weak quasiball norms obey the exact
second Phi inequality. Finiteness and source norm restriction are proved
from local Sobolev membership and the actual certified operator. -/
theorem quasiball_second_phi_with_constants {n q : ℕ} (G : HomogeneousGroup n)
    (ν : G2.HomogeneousNorm G) (X : Fin (q+1) → (Fin n → ℝ) → (Fin n → ℝ))
    (p : ℝ≥0∞) {C a b : ℝ} (hC : 0 ≤ C) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hstep : SecondQuasiballEstimate G ν X p C a b)
    (x₀ : Fin n → ℝ) {r : ℝ} (hr : 0 < r) (u : (Fin n → ℝ) → ℝ)
    (hu : memSobolevX driftWeight X (quasiballDomain G ν x₀ r) 2 p u)
    (D : WeakDriftOperatorData X (quasiballDomain G ν x₀ r) p u) :
    let N₀ := fun σ => (eLpNorm u p (volume.restrict (G2.gaugeBall G ν x₀ (σ*r)))).toReal
    let N₁ := fun σ => (horizontalWeakENorm X (quasiballDomain G ν x₀ (σ*r)) p u).toReal
    let N₂ := fun σ => (driftSecondWeakENorm X (quasiballDomain G ν x₀ (σ*r)) p u).toReal
    phi (Ioo (1/2 : ℝ) 1) r 2 N₂ ≤
      ENNReal.ofReal (C*r^2/4 *
        (eLpNorm D.operator p (volume.restrict (G2.gaugeBall G ν x₀ r))).toReal +
        8*a*C*(phi (Ioo (1/2 : ℝ) 1) r 1 N₁).toReal +
        4*b*C*(phi (Ioo (1/2 : ℝ) 1) r 0 N₀).toReal) := by
  exact second_phi_bound_of_midpoint_step _ _ _ hr hC ha hb ENNReal.toReal_nonneg
    (phi_quasiball_zero_lt_top G ν x₀ hr p u hu.1).ne
    (phi_horizontalWeak_lt_top G ν X x₀ hr p u hu).ne
    (quasiball_second_midpoint_with_constants G ν X p hC hstep x₀ hr u hu D)

end RothschildStein.H3
