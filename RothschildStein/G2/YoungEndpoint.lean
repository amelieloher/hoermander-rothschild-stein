-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.G2.NonnegativeConvolution
public import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
open MeasureTheory
open scoped ENNReal
namespace RothschildStein.G2
variable {N : ℕ} {𝕜 : Type*} [RCLike 𝕜] (G : HomogeneousGroup N)

/-- Hölder bound for the absolute convolution integrand, including
conjugate endpoint exponents (BB Prop 3.45, p. 119). -/
theorem eLpNorm_groupConvolution_integrand_le {p q : ℝ≥0∞}
    [p.HolderConjugate q] {f g : (Fin N → ℝ) → 𝕜}
    (hf : AEStronglyMeasurable f volume) (hg : AEStronglyMeasurable g volume)
    (x : Fin N → ℝ) :
    eLpNorm (fun y => f y * g (G.mul (G.inv y) x)) 1 volume ≤
      eLpNorm f p volume * eLpNorm g q volume := by
  have hmp := measurePreserving_invRightAt G x
  have hb := eLpNorm_smul_le_mul_eLpNorm (p := p) (q := q) hf (hg.comp_measurePreserving hmp)
    (r := (1 : ℝ≥0∞))
  change eLpNorm (fun y => f y * g (G.mul (G.inv y) x)) 1 volume ≤ _ at hb
  simpa only [eLpNorm_comp_measurePreserving hg hmp] using hb

/-- At the r = infinity endpoint the convolution exists at every
point, including (p,q) = (1,infinity) and (infinity,1) (BB p. 119). -/
theorem groupConvolutionExistsAt_of_memLp_conjugate {p q : ℝ≥0∞}
    [p.HolderConjugate q] {f g : (Fin N → ℝ) → 𝕜}
    (hf : MemLp f p volume) (hg : MemLp g q volume) (x : Fin N → ℝ) :
    GroupConvolutionExistsAt G f g x := by
  exact memLp_one_iff_integrable.mp
    (hf.mul (hg.comp_measurePreserving (measurePreserving_invRightAt G x)))

/-- The pointwise Young bound at r = infinity has constant one
(BB Prop 3.45, p. 119). -/
theorem enorm_groupConvolution_le_conjugate {p q : ℝ≥0∞}
    [p.HolderConjugate q] {f g : (Fin N → ℝ) → 𝕜}
    (hf : AEStronglyMeasurable f volume) (hg : AEStronglyMeasurable g volume)
    (x : Fin N → ℝ) :
    ‖groupConvolution G f g x‖ₑ ≤ eLpNorm f p volume * eLpNorm g q volume := by
  rw [groupConvolution_eq_integral]
  exact (enorm_integral_le_lintegral_enorm _).trans
    (lintegral_enorm_le_eLpNorm_one.trans
      (eLpNorm_groupConvolution_integrand_le G hf hg x))

end RothschildStein.G2
