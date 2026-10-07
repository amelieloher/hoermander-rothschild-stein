-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.G2.ConvolutionAbsolute

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
open MeasureTheory
open scoped ENNReal
namespace RothschildStein.G2
variable {N : ℕ} {𝕜 : Type*} [RCLike 𝕜] (G : HomogeneousGroup N)

private theorem young_input_ne_top {p q r : ℝ≥0∞}
    (hq : 1 ≤ q) (_hr : 1 ≤ r) (he : p⁻¹ + q⁻¹ = 1 + r⁻¹) (hrtop : r ≠ ⊤) : p ≠ ⊤ := by
  intro hptop
  have hqi : q⁻¹ ≤ 1 := by simpa using ENNReal.inv_le_inv.mpr hq
  have hbad : 1 + r⁻¹ ≤ 1 + 0 := by simpa [hptop] using (le_of_eq he.symm).trans (by simpa [hptop] using hqi)
  have hi : r⁻¹ ≤ 0 := (ENNReal.add_le_add_iff_left (by norm_num : (1 : ℝ≥0∞) ≠ ⊤)).mp hbad
  exact hrtop (ENNReal.inv_eq_zero.mp (le_antisymm hi bot_le))

/-- Young's inequality for extended exponents in [1,∞], with 1/p + 1/q = 1 + 1/r and constant one, including all endpoints (BB Proposition 3.45, p. 119). -/
theorem eLpNorm_groupConvolution_le {p q r : ℝ≥0∞}
    (hp : 1 ≤ p) (hq : 1 ≤ q) (hr : 1 ≤ r) (he : p⁻¹ + q⁻¹ = 1 + r⁻¹)
    {f g : (Fin N → ℝ) → 𝕜} (hf : AEStronglyMeasurable f volume)
    (hg : AEStronglyMeasurable g volume) :
    eLpNorm (groupConvolution G f g) r volume ≤ eLpNorm f p volume * eLpNorm g q volume := by
  by_cases hrtop : r = ⊤
  · have hconj : p.HolderConjugate q := ENNReal.holderConjugate_iff.mpr (by simpa [hrtop] using he)
    let : p.HolderConjugate q := hconj
    rw [hrtop]
    exact eLpNorm_groupConvolution_le_top G hf hg
  · have hptop := young_input_ne_top hq hr he hrtop
    have hqtop := young_input_ne_top hp hr (by simpa only [add_comm p⁻¹ q⁻¹] using he) hrtop
    have hpR : 1 ≤ p.toReal := by
      simpa using (ENNReal.toReal_le_toReal (by norm_num) hptop).mpr hp
    have hqR : 1 ≤ q.toReal := by
      simpa using (ENNReal.toReal_le_toReal (by norm_num) hqtop).mpr hq
    have hrR : 1 ≤ r.toReal := by
      simpa using (ENNReal.toReal_le_toReal (by norm_num) hrtop).mpr hr
    have hp0 : p ≠ 0 := (zero_lt_one.trans_le hp).ne'
    have hq0 : q ≠ 0 := (zero_lt_one.trans_le hq).ne'
    have hr0 : r ≠ 0 := (zero_lt_one.trans_le hr).ne'
    have hreal := congrArg ENNReal.toReal he
    rw [ENNReal.toReal_add (ENNReal.inv_ne_top.mpr hp0) (ENNReal.inv_ne_top.mpr hq0),
      ENNReal.toReal_add (by norm_num) (ENNReal.inv_ne_top.mpr hr0),
      ENNReal.toReal_one, ENNReal.toReal_inv, ENNReal.toReal_inv, ENNReal.toReal_inv] at hreal
    have H := eLpNorm_groupConvolution_le_finite_ae G hf hg hpR hqR hrR (by simpa only [one_div] using hreal)
    simpa only [ENNReal.ofReal_toReal hptop, ENNReal.ofReal_toReal hqtop,
      ENNReal.ofReal_toReal hrtop] using H

/-- Finite input norms give an Lr Bochner convolution throughout
the full Young range (BB Prop 3.45, p. 119). -/
theorem memLp_groupConvolution {p q r : ℝ≥0∞}
    (hp : 1 ≤ p) (hq : 1 ≤ q) (hr : 1 ≤ r) (he : p⁻¹ + q⁻¹ = 1 + r⁻¹)
    {f g : (Fin N → ℝ) → 𝕜} (hf : MemLp f p volume) (hg : MemLp g q volume) :
    MemLp (groupConvolution G f g) r volume :=
  (eLpNorm_groupConvolution_le G hp hq hr he hf.aestronglyMeasurable hg.aestronglyMeasurable).trans_lt
    (ENNReal.mul_lt_top hf.eLpNorm_lt_top hg.eLpNorm_lt_top)

end RothschildStein.G2
