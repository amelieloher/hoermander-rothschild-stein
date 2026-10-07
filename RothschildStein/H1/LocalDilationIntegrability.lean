-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H1.KernelScaling
public import Mathlib.MeasureTheory.Function.LocallyIntegrable

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public section
noncomputable section
open Set MeasureTheory
namespace RothschildStein.H1
variable {N : ℕ} (G : HomogeneousGroup N)

/-- Positive dilation preserves local integrability, by the exact
Jacobian and compact-set change of variables (BB p. 266). -/
theorem locallyIntegrable_comp_dilate {f : (Fin N → ℝ) → ℝ}
    (hf : LocallyIntegrable f) {t : ℝ} (ht : 0 < t) :
    LocallyIntegrable (fun x => f (G.dilate t x)) := by
  apply locallyIntegrable_iff.mpr
  intro K hK
  have hi := hf.integrableOn_isCompact (hK.image (G2.continuous_dilate G t))
  have hm : IntegrableOn f ((G.dilate t) '' K) (volume.map (G.dilate t)) := by
    rw [G2.map_dilate_volume G ht]
    change Integrable f ((ENNReal.ofReal ((t ^ G.homogeneousDimension)⁻¹) • volume).restrict
      ((G.dilate t) '' K))
    rw [Measure.restrict_smul]
    exact hi.smul_measure ENNReal.ofReal_ne_top
  have hcomp := (G2.measurableEmbedding_dilate G ht.ne').integrableOn_map_iff.mp hm
  exact hcomp.mono_set (subset_preimage_image (G.dilate t) K)

/-- Fundamental-kernel scaling retains the full L1-local
hypothesis required by the function-level weak regularity theorem (BB p. 266). -/
theorem locallyIntegrable_scaledFundamentalKernel {f : (Fin N → ℝ) → ℝ}
    (hf : LocallyIntegrable f) {s : ℝ} (hs : 0 < s) :
    LocallyIntegrable (scaledFundamentalKernel G s f) := by
  have h := (locallyIntegrable_comp_dilate G hf (inv_pos.mpr hs)).smul
    (s ^ 2 * (s ^ G.homogeneousDimension)⁻¹)
  exact h

end RothschildStein.H1
