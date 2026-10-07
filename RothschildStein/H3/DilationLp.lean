-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.G2.DilationMeasure
public import RothschildStein.G2.Gauge
public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
namespace RothschildStein.H3
open Set MeasureTheory
open scoped ENNReal
variable {N : ℕ} (G : HomogeneousGroup N)

/-- The global Lp dilation factor, including the inverse Jacobian
(BB pp. 356–357). -/
theorem eLpNorm_dilate (f : (Fin N → ℝ) → ℝ) (p : ℝ≥0∞)
    {t : ℝ} (ht : 0 < t) :
    eLpNorm (fun x => f (G.dilate t x)) p volume =
      ENNReal.ofReal ((t ^ G.homogeneousDimension)⁻¹) ^ (1 / p.toReal) *
        eLpNorm f p volume := by
  change eLpNorm (f ∘ G.dilate t) p volume = _
  rw [← (G2.measurableEmbedding_dilate G ht.ne').eLpNorm_map_measure,
    G2.map_dilate_volume G ht]
  simpa only [ENNReal.toReal_div, ENNReal.toReal_one, smul_eq_mul] using
    eLpNorm_smul_measure_of_ne_zero
      (c := ENNReal.ofReal ((t ^ G.homogeneousDimension)⁻¹))
      (ENNReal.ofReal_pos.mpr (inv_pos.mpr (pow_pos ht _))).ne' f p volume

end RothschildStein.H3
