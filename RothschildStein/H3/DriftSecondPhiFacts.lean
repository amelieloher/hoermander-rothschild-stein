-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H3.DriftSecondNormComparison
public import RothschildStein.H3.QuasiballDomainRestriction
public import RothschildStein.H3.PhiBounds

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
namespace RothschildStein.H3
open Set MeasureTheory TopologicalSpace
open scoped ENNReal

/-- The full second Phi is finite for actual local Sobolev data. -/
theorem phi_driftSecond_lt_top {n q : ℕ} (G : HomogeneousGroup n)
    (ν : G2.HomogeneousNorm G) (X : Fin (q+1) → (Fin n → ℝ) → (Fin n → ℝ))
    (x₀ : Fin n → ℝ) {r : ℝ} (hr : 0 < r) (p : ℝ≥0∞) (u : (Fin n → ℝ) → ℝ)
    (hu : memSobolevX driftWeight X (quasiballDomain G ν x₀ r) 2 p u) :
    phi (Ioo (1/2 : ℝ) 1) r 2
      (fun σ => (driftSecondWeakENorm X (quasiballDomain G ν x₀ (σ*r)) p u).toReal) < ⊤ := by
  apply phi_lt_top_of_uniform_bound _ _ 2 hr ENNReal.toReal_nonneg
    (fun _ h => ⟨h.1.le,h.2⟩)
  intro σ hσ
  refine ⟨ENNReal.toReal_nonneg, ?_⟩
  exact ENNReal.toReal_mono (driftSecondWeakENorm_lt_top X _ p u hu).ne
    (driftSecondWeakENorm_mono_domain X _ _
      (quasiballDomain_subset_of_le G ν x₀ (by nlinarith [hσ.2])) p u hu)

/-- The half-radius complete second norm has the exact Phi
lower bound, without requiring norm continuity at the endpoint. -/
theorem phi_driftSecond_half_radius_le {n q : ℕ} (G : HomogeneousGroup n)
    (ν : G2.HomogeneousNorm G) (X : Fin (q+1) → (Fin n → ℝ) → (Fin n → ℝ))
    (x₀ : Fin n → ℝ) {r : ℝ} (hr : 0 < r) (p : ℝ≥0∞) (u : (Fin n → ℝ) → ℝ)
    (hu : memSobolevX driftWeight X (quasiballDomain G ν x₀ r) 2 p u) :
    ENNReal.ofReal ((r/2)^2 *
      (driftSecondWeakENorm X (quasiballDomain G ν x₀ (r/2)) p u).toReal) ≤
      phi (Ioo (1/2 : ℝ) 1) r 2
        (fun σ => (driftSecondWeakENorm X (quasiballDomain G ν x₀ (σ*r)) p u).toReal) := by
  apply phi_half_radius_le 2 hr ENNReal.toReal_nonneg
  intro σ hσ
  have hs := memSobolevX_quasiball_restrict G ν x₀ (by nlinarith [hσ.2] : σ*r ≤ r)
    driftWeight X 2 p u hu
  exact ENNReal.toReal_mono (driftSecondWeakENorm_lt_top X _ p u hs).ne
    (driftSecondWeakENorm_mono_domain X _ _
      (quasiballDomain_subset_of_le G ν x₀ (by nlinarith [hσ.1] : r/2 ≤ σ*r)) p u hs)

/-- The diagonal second Phi is bounded by the complete weighted second
Phi used in the half-radius estimate. -/
theorem phi_horizontalSquare_le_driftSecond {n q : ℕ} (G : HomogeneousGroup n)
    (ν : G2.HomogeneousNorm G) (X : Fin (q+1) → (Fin n → ℝ) → (Fin n → ℝ))
    (x₀ : Fin n → ℝ) {r : ℝ} (hr : 0 < r) (p : ℝ≥0∞) (u : (Fin n → ℝ) → ℝ)
    (hu : memSobolevX driftWeight X (quasiballDomain G ν x₀ r) 2 p u) :
    phi (Ioo (1/2 : ℝ) 1) r 2
      (fun σ => (horizontalSquareWeakENorm X (quasiballDomain G ν x₀ (σ*r)) p u).toReal) ≤
      phi (Ioo (1/2 : ℝ) 1) r 2
        (fun σ => (driftSecondWeakENorm X (quasiballDomain G ν x₀ (σ*r)) p u).toReal) := by
  apply iSup_mono
  intro σ
  apply iSup_mono
  intro hσ
  have hs := memSobolevX_quasiball_restrict G ν x₀ (by nlinarith [hσ.2] : σ*r ≤ r)
    driftWeight X 2 p u hu
  have hn := ENNReal.toReal_mono (driftSecondWeakENorm_lt_top X _ p u hs).ne
    (horizontalSquareWeakENorm_le_driftSecond X _ p u)
  exact ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left hn (by positivity))

end RothschildStein.H3
