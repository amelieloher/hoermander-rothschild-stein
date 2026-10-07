-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H3.QuasiballDomain
public import RothschildStein.H3.PhiBounds

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
namespace RothschildStein.H3
open Set MeasureTheory
open scoped ENNReal
variable {n : ℕ}

/-- Step 2: every local zero Phi is bounded by the global input
norm; no derivative or local regularity assumptions are used. -/
theorem phi_zero_bound_of_global_memLp
    (G : HomogeneousGroup n) (ν : G2.HomogeneousNorm G)
    {u : (Fin n → ℝ) → ℝ} {p : ℝ≥0∞}
    (hu : MemLp u p (volume : Measure (Fin n → ℝ)))
    (x₀ : Fin n → ℝ) {R : ℝ} (hR : 0 < R) :
    phi (Ioo (1 / 2 : ℝ) 1) R 0
      (fun σ => (eLpNorm u p (volume.restrict (G2.gaugeBall G ν x₀ (σ * R)))).toReal) ≤
      ENNReal.ofReal (eLpNorm u p volume).toReal := by
  have hb := phi_le_uniform_bound (B := (eLpNorm u p volume).toReal)
    (N := fun σ => (eLpNorm u p (volume.restrict (G2.gaugeBall G ν x₀ (σ * R)))).toReal)
    (Ioo (1 / 2 : ℝ) 1) 0 hR ENNReal.toReal_nonneg (fun _ h => ⟨h.1.le, h.2⟩)
    (fun σ _ => ⟨ENNReal.toReal_nonneg, ENNReal.toReal_mono hu.eLpNorm_lt_top.ne
      (eLpNorm_mono_measure u Measure.restrict_le_self)⟩)
  simpa only [pow_zero, one_mul] using hb

end RothschildStein.H3
