-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H3.TypeZeroTail
public import RothschildStein.G2.Young

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
namespace RothschildStein.H3
open MeasureTheory
open scoped ENNReal
variable {N : ℕ} (G : HomogeneousGroup N)

/-- The finite annular tail defines a bounded Lp convolution, with a
geometric coefficient linear in the actual kernel sphere seminorm. -/
theorem TypeZero.unitTail_convolution_memLp_and_bound {ν : G2.HomogeneousNorm G}
    {k : (Fin N → ℝ) → ℝ} (hk : TypeZero G ν k)
    {p : ℝ≥0∞} (hp : 1 ≤ p) {u : (Fin N → ℝ) → ℝ} (hu : MemLp u p volume) :
    MemLp (G2.groupConvolution G u (typeZeroUnitTail ν k)) p volume ∧
      eLpNorm (G2.groupConvolution G u (typeZeroUnitTail ν k)) p volume ≤
        (ENNReal.ofReal (kernelSphereBound ν k) * volume {x | 1 ≤ ν x ∧ ν x ≤ 2}) *
          eLpNorm u p volume := by
  obtain ⟨hi, hb⟩ := hk.unitTail_integrable_and_bound
  have ht : MemLp (typeZeroUnitTail ν k) 1 volume := memLp_one_iff_integrable.mpr hi
  have he : p⁻¹ + (1 : ℝ≥0∞)⁻¹ = 1 + p⁻¹ := by simp only [inv_one, add_comm]
  refine ⟨G2.memLp_groupConvolution G hp le_rfl hp he hu ht, ?_⟩
  calc
    _ ≤ eLpNorm u p volume * eLpNorm (typeZeroUnitTail ν k) 1 volume :=
      G2.eLpNorm_groupConvolution_le G hp le_rfl hp he hu.aestronglyMeasurable hi.aestronglyMeasurable
    _ ≤ eLpNorm u p volume *
        (ENNReal.ofReal (kernelSphereBound ν k) * volume {x | 1 ≤ ν x ∧ ν x ≤ 2}) :=
      mul_le_mul' le_rfl hb
    _ = _ := mul_comm _ _

end RothschildStein.H3
