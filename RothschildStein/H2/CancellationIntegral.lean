-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.MeasureTheory.Integral.Prod

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set MeasureTheory
open scoped ENNReal

namespace RothschildStein.H2
variable {X : Type*} [MeasurableSpace X]

/-- Cancellation subtracts a constant kernel value using the
zero integral of a bad piece (BB p. 320). -/
theorem integral_kernel_cancel (μ : Measure X) (k b : X → ℝ) (c : ℝ)
    (hb : Integrable b μ) (hk : Integrable (fun x => k x * b x) μ)
    (hzero : (∫ x, b x ∂μ) = 0) :
    (∫ x, (k x - c) * b x ∂μ) = ∫ x, k x * b x ∂μ := by
  simp_rw [sub_mul]
  rw [integral_sub hk (hb.const_mul c), integral_const_mul, hzero, mul_zero, sub_zero]

/-- Tonelli converts a uniform kernel tail bound to the L¹
bound of the cancelled integral against a bad piece (BB p. 320). -/
theorem cancellation_integral_l1_bound (μ : Measure X) {B Y : Set X}
    (hB : MeasurableSet B) (_hY : MeasurableSet Y)
    (hμB : μ B ≠ ∞) (hμY : μ Y ≠ ∞)
    (k : X → X → ℝ) (hk : Measurable (Function.uncurry k))
    (b : X → ℝ) (hb : Measurable b) (C : ℝ≥0∞)
    (htail : ∀ x ∈ B, (∫⁻ y in Y, ‖k y x‖ₑ ∂μ) ≤ C) :
    (∫⁻ y in Y, ‖∫ x in B, k y x * b x ∂μ‖ₑ ∂μ) ≤
      C * ∫⁻ x in B, ‖b x‖ₑ ∂μ := by
  let : IsFiniteMeasure (μ.restrict B) := ⟨by simpa using hμB.lt_top⟩
  let : IsFiniteMeasure (μ.restrict Y) := ⟨by simpa using hμY.lt_top⟩
  have hm : Measurable (fun p : X × X => ‖k p.1 p.2‖ₑ * ‖b p.2‖ₑ) :=
    hk.enorm.mul (hb.enorm.comp measurable_snd)
  calc
    _ ≤ ∫⁻ y in Y, ∫⁻ x in B, ‖k y x‖ₑ * ‖b x‖ₑ ∂μ ∂μ := by
      apply lintegral_mono
      intro y
      simpa only [enorm_mul] using enorm_integral_le_lintegral_enorm (fun x => k y x * b x)
    _ = ∫⁻ x in B, ∫⁻ y in Y, ‖k y x‖ₑ * ‖b x‖ₑ ∂μ ∂μ :=
      lintegral_lintegral_swap hm.aemeasurable
    _ ≤ ∫⁻ x in B, C * ‖b x‖ₑ ∂μ := by
      apply setLIntegral_mono' hB
      intro x hx
      have hxmeas : AEMeasurable (fun y => ‖k y x‖ₑ) (μ.restrict Y) :=
        (hk.comp (measurable_id.prodMk (measurable_const (a := x)))).enorm.aemeasurable
      rw [lintegral_mul_const'' _ hxmeas]
      exact mul_le_mul' (htail x hx) le_rfl
    _ = _ := lintegral_const_mul'' C hb.enorm.aemeasurable

end RothschildStein.H2
