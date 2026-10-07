-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.G2.YoungNorm
public import RothschildStein.G2.YoungEndpoint

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
open MeasureTheory Filter
open scoped ENNReal
namespace RothschildStein.G2
variable {N : ℕ} {𝕜 : Type*} [RCLike 𝕜] (G : HomogeneousGroup N)

/-- Finite-output Young inequality for measurable equivalence classes
(BB Prop 3.45, p. 119). -/
theorem eLpNorm_groupConvolution_le_finite_ae {f g : (Fin N → ℝ) → 𝕜}
    (hf : AEStronglyMeasurable f volume) (hg : AEStronglyMeasurable g volume) {p q r : ℝ}
    (hp : 1 ≤ p) (hq : 1 ≤ q) (hr : 1 ≤ r)
    (he : 1 / p + 1 / q = 1 + 1 / r) :
    eLpNorm (groupConvolution G f g) (ENNReal.ofReal r) volume ≤
      eLpNorm f (ENNReal.ofReal p) volume * eLpNorm g (ENNReal.ofReal q) volume := by
  have hfg : groupConvolution G f g = groupConvolution G (hf.mk f) (hg.mk g) :=
    funext (groupConvolution_congr_ae G hf.ae_eq_mk hg.ae_eq_mk)
  rw [hfg, eLpNorm_congr_ae hf.ae_eq_mk, eLpNorm_congr_ae hg.ae_eq_mk]
  exact eLpNorm_groupConvolution_le_finite G hf.stronglyMeasurable_mk
    hg.stronglyMeasurable_mk hp hq hr he

/-- Young's inequality at output infinity, including input endpoint
exponents one and infinity (BB p. 119). -/
theorem eLpNorm_groupConvolution_le_top {p q : ℝ≥0∞} [p.HolderConjugate q]
    {f g : (Fin N → ℝ) → 𝕜} (hf : AEStronglyMeasurable f volume)
    (hg : AEStronglyMeasurable g volume) :
    eLpNorm (groupConvolution G f g) ⊤ volume ≤ eLpNorm f p volume * eLpNorm g q volume := by
  rw [eLpNorm_exponent_top (aestronglyMeasurable_groupConvolution G hf hg)]
  exact eLpNormEssSup_le_of_ae_enorm_bound (Eventually.of_forall
    (enorm_groupConvolution_le_conjugate G hf hg))

end RothschildStein.G2
