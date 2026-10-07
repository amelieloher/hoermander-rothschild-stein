-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
public import Mathlib.MeasureTheory.Integral.MeanInequalities

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
open MeasureTheory
open scoped ENNReal
namespace RothschildStein.S
variable {α : Type*} [MeasurableSpace α] {μ : Measure α}

/-- A finite positive Lp norm raised to p is exactly its
integrated p-th extended norm (BB Lemma 2.11, p. 74). -/
theorem lintegral_enorm_rpow_eq_eLpNorm_rpow
    {f : α → ℝ} {p : ℝ≥0∞} (hp0 : p ≠ 0) (hpt : p ≠ ⊤)
    (hf : AEStronglyMeasurable f μ) :
    (∫⁻ x, ‖f x‖ₑ^p.toReal ∂μ) = (eLpNorm f p μ)^p.toReal := by
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 hpt hf,← ENNReal.rpow_mul,
    one_div_mul_cancel (ENNReal.toReal_ne_zero.mpr ⟨hp0,hpt⟩),ENNReal.rpow_one]

/-- The Jensen and Tonelli mass factors combine into the exact
p-th power of C·mass·modulus, including p=1 and zero factors
(BB Lemma 2.11, p. 74). -/
theorem kernelMoment_factors_eq_rpow (C mass M : ℝ≥0∞) {p : ℝ} (hp : 1 ≤ p) :
    C^p * mass^(p-1) * (mass * M^p) = (C*mass*M)^p := by
  have hp0 : 0 ≤ p := le_trans zero_le_one hp
  have hm : mass^(p-1) * mass = mass^p := by
    nth_rw 2 [← ENNReal.rpow_one mass]
    rw [← ENNReal.rpow_add_of_nonneg (p-1) 1 (sub_nonneg.mpr hp) zero_le_one,
      sub_add_cancel]
  calc
    _ = C^p * (mass^(p-1)*mass) * M^p := by ac_rfl
    _ = C^p * mass^p * M^p := by rw [hm]
    _ = _ := by simp only [ENNReal.mul_rpow_of_nonneg _ _ hp0]

end RothschildStein.S
