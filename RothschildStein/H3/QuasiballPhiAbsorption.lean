-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H3.QuasiballSecondPhi
public import RothschildStein.H3.DriftSecondPhiFacts
public import RothschildStein.H3.PhiSecondAbsorption

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
namespace RothschildStein.H3
open Set MeasureTheory
open scoped ENNReal

/-- Step 2: absorption for the actual local quasiball Phi values. -/
theorem quasiball_phi_absorbed_with_constants {n q : ℕ} (G : HomogeneousGroup n)
    (ν : G2.HomogeneousNorm G) (X : Fin (q+1) → (Fin n → ℝ) → (Fin n → ℝ))
    (p : ℝ≥0∞) {C a b cE δ : ℝ}
    (hC : 0 ≤ C) (ha : 0 ≤ a) (hb : 0 ≤ b) (hcE : 0 ≤ cE)
    (hδ : 0 < δ) (hsmall : (8*a*C)*δ ≤ 1/2)
    (hstep : SecondQuasiballEstimate G ν X p C a b)
    (x₀ : Fin n → ℝ) {r : ℝ} (hr : 0 < r) (u : (Fin n → ℝ) → ℝ)
    (hu : memSobolevX driftWeight X (quasiballDomain G ν x₀ r) 2 p u)
    (D : WeakDriftOperatorData X (quasiballDomain G ν x₀ r) p u) :
    let P₀ := phi (Ioo (1/2 : ℝ) 1) r 0
      (fun σ => (eLpNorm u p (volume.restrict (G2.gaugeBall G ν x₀ (σ*r)))).toReal)
    let P₁ := phi (Ioo (1/2 : ℝ) 1) r 1
      (fun σ => (horizontalWeakENorm X (quasiballDomain G ν x₀ (σ*r)) p u).toReal)
    let P₂ := phi (Ioo (1/2 : ℝ) 1) r 2
      (fun σ => (driftSecondWeakENorm X (quasiballDomain G ν x₀ (σ*r)) p u).toReal)
    let F := (eLpNorm D.operator p (volume.restrict (G2.gaugeBall G ν x₀ r))).toReal
    P₁ ≤ ENNReal.ofReal δ*P₂ + ENNReal.ofReal (cE/δ)*P₀ →
      P₂.toReal ≤ C*r^2/2*F + 2*(4*b*C+(8*a*C)*cE/δ)*P₀.toReal ∧
      P₁.toReal ≤ δ*(C*r^2/2*F + 2*(4*b*C+(8*a*C)*cE/δ)*P₀.toReal) +
        cE/δ*P₀.toReal := by
  dsimp only
  intro hfirst
  exact phi_second_absorbed_bounds
    (phi_quasiball_zero_lt_top G ν x₀ hr p u hu.1).ne
    (phi_driftSecond_lt_top G ν X x₀ hr p u hu).ne
    hC (by positivity) (by positivity) hcE ENNReal.toReal_nonneg hδ hsmall
    (quasiball_second_phi_with_constants G ν X p hC ha hb hstep x₀ hr u hu D) hfirst

end RothschildStein.H3
