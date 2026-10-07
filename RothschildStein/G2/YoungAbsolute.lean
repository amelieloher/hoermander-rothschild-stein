-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.G2.Young

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
open MeasureTheory Filter
open scoped ENNReal
namespace RothschildStein.G2
variable {N : ℕ} {𝕜 : Type*} [RCLike 𝕜] (G : HomogeneousGroup N)

private theorem input_ne_top {p q r : ℝ≥0∞} (hq : 1 ≤ q)
    (he : p⁻¹ + q⁻¹ = 1 + r⁻¹) (hrtop : r ≠ ⊤) : p ≠ ⊤ := by
  intro hptop
  have hqi : q⁻¹ ≤ 1 := by simpa using ENNReal.inv_le_inv.mpr hq
  have hbad : 1 + r⁻¹ ≤ 1 + 0 := by
    simpa [hptop] using (le_of_eq he.symm).trans (by simpa [hptop] using hqi)
  have hi : r⁻¹ ≤ 0 :=
    (ENNReal.add_le_add_iff_left (by norm_num : (1 : ℝ≥0∞) ≠ ⊤)).mp hbad
  exact hrtop (ENNReal.inv_eq_zero.mp (le_antisymm hi bot_le))

/-- Absolute convergence almost everywhere for the full Young
range, including endpoint exponents (BB Prop 3.45, p. 119). For r = infinity
absolute convergence holds at every point by the conjugate endpoint lemma. -/
theorem groupConvolutionExistsAt_ae_extended {p q r : ℝ≥0∞}
    (hp : 1 ≤ p) (hq : 1 ≤ q) (hr : 1 ≤ r) (he : p⁻¹ + q⁻¹ = 1 + r⁻¹)
    {f g : (Fin N → ℝ) → 𝕜} (hf : MemLp f p volume) (hg : MemLp g q volume) :
    ∀ᵐ x ∂volume, GroupConvolutionExistsAt G f g x := by
  by_cases hrtop : r = ⊤
  · let : p.HolderConjugate q := ENNReal.holderConjugate_iff.mpr (by simpa [hrtop] using he)
    exact Eventually.of_forall (groupConvolutionExistsAt_of_memLp_conjugate G hf hg)
  · have hptop := input_ne_top hq he hrtop
    have hqtop := input_ne_top hp (by simpa only [add_comm p⁻¹ q⁻¹] using he) hrtop
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
    have hf' : MemLp f (ENNReal.ofReal p.toReal) volume := by
      simpa only [ENNReal.ofReal_toReal hptop] using hf
    have hg' : MemLp g (ENNReal.ofReal q.toReal) volume := by
      simpa only [ENNReal.ofReal_toReal hqtop] using hg
    exact groupConvolutionExistsAt_ae G hpR hqR hrR (by simpa only [one_div] using hreal) hf' hg'

end RothschildStein.G2
