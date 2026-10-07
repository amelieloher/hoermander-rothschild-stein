-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H3.QuasiballDomainRestriction
public import RothschildStein.H3.PhiBounds

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
namespace RothschildStein.H3
open Set MeasureTheory
open scoped ENNReal

/-- The actual zeroth Phi is bounded by the full quasiball norm. -/
theorem phi_quasiball_zero_le {n : ℕ} (G : HomogeneousGroup n)
    (ν : G2.HomogeneousNorm G) (x₀ : Fin n → ℝ) {r : ℝ} (hr : 0 < r)
    (p : ℝ≥0∞) (u : (Fin n → ℝ) → ℝ)
    (hu : MemLp u p (volume.restrict (G2.gaugeBall G ν x₀ r))) :
    phi (Ioo (1/2 : ℝ) 1) r 0
      (fun σ => (eLpNorm u p (volume.restrict (G2.gaugeBall G ν x₀ (σ*r)))).toReal) ≤
      ENNReal.ofReal ((eLpNorm u p (volume.restrict (G2.gaugeBall G ν x₀ r))).toReal) := by
  have hb := phi_le_uniform_bound
    (B := (eLpNorm u p (volume.restrict (G2.gaugeBall G ν x₀ r))).toReal) (Ioo (1/2 : ℝ) 1)
    (fun σ => (eLpNorm u p (volume.restrict (G2.gaugeBall G ν x₀ (σ*r)))).toReal)
    0 hr ENNReal.toReal_nonneg (fun _ h => ⟨h.1.le,h.2⟩) (fun σ hσ => ?_)
  · simpa only [pow_zero, one_mul] using hb
  · refine ⟨ENNReal.toReal_nonneg, ?_⟩
    apply ENNReal.toReal_mono hu.eLpNorm_ne_top
    exact eLpNorm_mono_measure u (Measure.restrict_mono_set volume
      (quasiballDomain_subset_of_le G ν x₀ (by nlinarith [hσ.2] : σ*r ≤ r)))

/-- The zeroth Phi is finite by the actual full-ball Lp membership. -/
theorem phi_quasiball_zero_lt_top {n : ℕ} (G : HomogeneousGroup n)
    (ν : G2.HomogeneousNorm G) (x₀ : Fin n → ℝ) {r : ℝ} (hr : 0 < r)
    (p : ℝ≥0∞) (u : (Fin n → ℝ) → ℝ)
    (hu : MemLp u p (volume.restrict (G2.gaugeBall G ν x₀ r))) :
    phi (Ioo (1/2 : ℝ) 1) r 0
      (fun σ => (eLpNorm u p (volume.restrict (G2.gaugeBall G ν x₀ (σ*r)))).toReal) < ⊤ :=
  (phi_quasiball_zero_le G ν x₀ hr p u hu).trans_lt ENNReal.ofReal_lt_top

end RothschildStein.H3
