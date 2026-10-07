-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H3.QuasiballPhiAbsorption
public import RothschildStein.H3.QuasiballHalfRadius

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
namespace RothschildStein.H3
open Set MeasureTheory
open scoped ENNReal

/-- actual local Sobolev and operator data give the
scale-invariant half-radius bound from the second step and interpolation. -/
theorem halfRadius_estimate_with_constants {n q : ℕ} (G : HomogeneousGroup n)
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
    let B := 2*(4*b*C+(8*a*C)*cE/δ)
    let K := 1+(4+2*δ)*(C/2)+(4+2*δ)*B+2*cE/δ
    P₁ ≤ ENNReal.ofReal δ*P₂ + ENNReal.ofReal (cE/δ)*P₀ →
    0 < K ∧
      (driftSecondWeakENorm X (quasiballDomain G ν x₀ (r/2)) p u).toReal +
      r⁻¹*(horizontalWeakENorm X (quasiballDomain G ν x₀ (r/2)) p u).toReal +
      r⁻¹^2*(eLpNorm u p (volume.restrict (G2.gaugeBall G ν x₀ (r/2)))).toReal ≤
      K*((eLpNorm D.operator p (volume.restrict (G2.gaugeBall G ν x₀ r))).toReal+
        r⁻¹^2*(eLpNorm u p (volume.restrict (G2.gaugeBall G ν x₀ r))).toReal) := by
  dsimp only
  intro hfirst
  obtain ⟨h₂,h₁⟩ := quasiball_phi_absorbed_with_constants G ν X p
    hC ha hb hcE hδ hsmall hstep x₀ hr u hu D hfirst
  have hzero := ENNReal.toReal_mono ENNReal.ofReal_ne_top
    (phi_quasiball_zero_le G ν x₀ hr p u hu.1)
  rw [ENNReal.toReal_ofReal ENNReal.toReal_nonneg] at hzero
  have hB : 0 ≤ 2*(4*b*C+(8*a*C)*cE/δ) := by positivity
  apply quasiball_halfRadius_of_absorbed_phi G ν X p x₀ hr u hu
    (show 0 ≤ C/2 by positivity) hB hδ hcE ENNReal.toReal_nonneg
  · have hh := h₂.trans (add_le_add le_rfl (mul_le_mul_of_nonneg_left hzero hB))
    simpa only [div_mul_eq_mul_div] using hh
  · have hh := h₁.trans (add_le_add
      (mul_le_mul_of_nonneg_left
        (add_le_add le_rfl (mul_le_mul_of_nonneg_left hzero hB)) hδ.le)
      (mul_le_mul_of_nonneg_left hzero (div_nonneg hcE hδ.le)))
    simpa only [div_mul_eq_mul_div] using hh

end RothschildStein.H3
