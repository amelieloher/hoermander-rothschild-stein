-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H3.HalfRadiusScalarEstimate
public import RothschildStein.H3.QuasiballZeroPhi
public import RothschildStein.H3.DriftSecondPhiFacts
public import RothschildStein.H3.HorizontalPhiHalfRadius

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
namespace RothschildStein.H3
open Set MeasureTheory
open scoped ENNReal

/-- Actual half-radius weak norms satisfy the scale-invariant estimate
once the two full-second absorbed Phi bounds are supplied. -/
theorem quasiball_halfRadius_of_absorbed_phi {n q : ℕ} (G : HomogeneousGroup n)
    (ν : G2.HomogeneousNorm G) (X : Fin (q+1) → (Fin n → ℝ) → (Fin n → ℝ))
    (p : ℝ≥0∞) (x₀ : Fin n → ℝ) {r : ℝ} (hr : 0 < r)
    (u : (Fin n → ℝ) → ℝ)
    (hu : memSobolevX driftWeight X (quasiballDomain G ν x₀ r) 2 p u)
    {A B δ cE F : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) (hδ : 0 < δ)
    (hcE : 0 ≤ cE) (hF : 0 ≤ F) :
    let U := (eLpNorm u p (volume.restrict (G2.gaugeBall G ν x₀ r))).toReal
    let P₁ := phi (Ioo (1/2 : ℝ) 1) r 1
      (fun σ => (horizontalWeakENorm X (quasiballDomain G ν x₀ (σ*r)) p u).toReal)
    let P₂ := phi (Ioo (1/2 : ℝ) 1) r 2
      (fun σ => (driftSecondWeakENorm X (quasiballDomain G ν x₀ (σ*r)) p u).toReal)
    let K := 1+(4+2*δ)*A+(4+2*δ)*B+2*cE/δ
    P₂.toReal ≤ A*r^2*F+B*U →
    P₁.toReal ≤ δ*(A*r^2*F+B*U)+cE/δ*U →
    0 < K ∧
      (driftSecondWeakENorm X (quasiballDomain G ν x₀ (r/2)) p u).toReal +
      r⁻¹*(horizontalWeakENorm X (quasiballDomain G ν x₀ (r/2)) p u).toReal +
      r⁻¹^2*(eLpNorm u p (volume.restrict (G2.gaugeBall G ν x₀ (r/2)))).toReal ≤
      K*(F+r⁻¹^2*U) := by
  dsimp only
  intro h₂ h₁
  apply halfRadius_scalar_estimate hr hA hB hδ hcE hF ENNReal.toReal_nonneg h₂ h₁
  · exact (ENNReal.ofReal_le_iff_le_toReal
      (phi_driftSecond_lt_top G ν X x₀ hr p u hu).ne).mp
      (phi_driftSecond_half_radius_le G ν X x₀ hr p u hu)
  · exact (ENNReal.ofReal_le_iff_le_toReal
      (phi_horizontalWeak_lt_top G ν X x₀ hr p u hu).ne).mp
      (phi_horizontalWeak_half_radius_le G ν X x₀ hr p u hu)
  · exact ENNReal.toReal_mono hu.1.eLpNorm_ne_top
      (eLpNorm_mono_measure u (Measure.restrict_mono_set volume
        (quasiballDomain_subset_of_le G ν x₀ (by linarith : r/2 ≤ r))))

end RothschildStein.H3
