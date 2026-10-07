-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.G2.YoungLp

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
open MeasureTheory Filter
open scoped ENNReal
namespace RothschildStein.G2
variable {N : ℕ} {𝕜 : Type*} [RCLike 𝕜] (G : HomogeneousGroup N)

/-- Absolute convergence is precisely finiteness of the nonnegative
convolution of norms (BB Def 3.44, pp. 118–119). -/
theorem groupConvolutionExistsAt_iff {f g : (Fin N → ℝ) → 𝕜}
    (hf : AEStronglyMeasurable f volume) (hg : AEStronglyMeasurable g volume)
    (x : Fin N → ℝ) : GroupConvolutionExistsAt G f g x ↔
      lgroupConvolution G (fun y => ‖f y‖ₑ) (fun y => ‖g y‖ₑ) x < ⊤ := by
  have hm : AEStronglyMeasurable (fun y => f y * g (G.mul (G.inv y) x)) volume :=
    hf.mul (hg.comp_measurePreserving (measurePreserving_invRightAt G x))
  change Integrable (fun y => f y * g (G.mul (G.inv y) x)) volume ↔ _
  rw [Integrable, and_iff_right hm, hasFiniteIntegral_iff_enorm]
  simp only [lgroupConvolution_def, enorm_mul]

/-- Finite-output Young gives absolute convergence almost everywhere
for strongly measurable representatives (BB Prop 3.45, p. 119). -/
theorem groupConvolutionExistsAt_ae_strong {f g : (Fin N → ℝ) → 𝕜} {p q r : ℝ}
    (hp : 1 ≤ p) (hq : 1 ≤ q) (hr : 1 ≤ r)
    (he : 1 / p + 1 / q = 1 + 1 / r)
    (hf : MemLp f (ENNReal.ofReal p) volume) (hg : MemLp g (ENNReal.ofReal q) volume)
    (hfm : StronglyMeasurable f) (hgm : StronglyMeasurable g) :
    ∀ᵐ x ∂volume, GroupConvolutionExistsAt G f g x := by
  have hp0 : 0 < p := lt_of_lt_of_le zero_lt_one hp
  have hq0 : 0 < q := lt_of_lt_of_le zero_lt_one hq
  have hr0 : 0 < r := lt_of_lt_of_le zero_lt_one hr
  have hpint : (∫⁻ x, ‖f x‖ₑ ^ p) < ⊤ := by
    simpa only [ENNReal.toReal_ofReal hp0.le] using
      lintegral_rpow_enorm_lt_top_of_eLpNorm_lt_top (ENNReal.ofReal_pos.mpr hp0).ne'
        ENNReal.ofReal_ne_top hf.eLpNorm_lt_top
  have hqint : (∫⁻ x, ‖g x‖ₑ ^ q) < ⊤ := by
    simpa only [ENNReal.toReal_ofReal hq0.le] using
      lintegral_rpow_enorm_lt_top_of_eLpNorm_lt_top (ENNReal.ofReal_pos.mpr hq0).ne'
        ENNReal.ofReal_ne_top hg.eLpNorm_lt_top
  have H := young_groupConvolution_power G hfm.measurable.enorm hgm.measurable.enorm hp hq hr he
  have hfin := H.trans_lt (ENNReal.mul_lt_top
    (ENNReal.rpow_lt_top_of_nonneg (div_nonneg hr0.le hp0.le) hpint.ne)
    (ENNReal.rpow_lt_top_of_nonneg (div_nonneg hr0.le hq0.le) hqint.ne))
  have hpoint := ae_lt_top ((measurable_lgroupConvolution G hfm.measurable.enorm
    hgm.measurable.enorm).pow_const r) hfin.ne
  filter_upwards [hpoint] with x hx
  exact (groupConvolutionExistsAt_iff G hf.aestronglyMeasurable hg.aestronglyMeasurable x).mpr
    ((ENNReal.rpow_lt_top_iff_of_pos hr0).mp hx)

/-- Finite input norms give absolute convergence almost everywhere,
independently of the chosen measurable representatives (BB p. 119). -/
theorem groupConvolutionExistsAt_ae {f g : (Fin N → ℝ) → 𝕜} {p q r : ℝ}
    (hp : 1 ≤ p) (hq : 1 ≤ q) (hr : 1 ≤ r)
    (he : 1 / p + 1 / q = 1 + 1 / r)
    (hf : MemLp f (ENNReal.ofReal p) volume) (hg : MemLp g (ENNReal.ofReal q) volume) :
    ∀ᵐ x ∂volume, GroupConvolutionExistsAt G f g x := by
  let fm := hf.aestronglyMeasurable
  let gm := hg.aestronglyMeasurable
  have hf0 : MemLp (fm.mk f) (ENNReal.ofReal p) volume := by
    change eLpNorm (fm.mk f) _ _ < ⊤
    rw [← eLpNorm_congr_ae fm.ae_eq_mk]
    exact hf
  have hg0 : MemLp (gm.mk g) (ENNReal.ofReal q) volume := by
    change eLpNorm (gm.mk g) _ _ < ⊤
    rw [← eLpNorm_congr_ae gm.ae_eq_mk]
    exact hg
  have H := groupConvolutionExistsAt_ae_strong G hp hq hr he hf0 hg0
    fm.stronglyMeasurable_mk gm.stronglyMeasurable_mk
  filter_upwards [H] with x hx
  apply (groupConvolutionExistsAt_iff G fm gm x).mpr
  rw [lgroupConvolution_congr_ae G (fm.ae_eq_mk.mono fun _ hy => congrArg (fun z => ‖z‖ₑ) hy)
    (gm.ae_eq_mk.mono fun _ hy => congrArg (fun z => ‖z‖ₑ) hy) x]
  exact (groupConvolutionExistsAt_iff G hf0.aestronglyMeasurable hg0.aestronglyMeasurable x).mp hx

end RothschildStein.G2
