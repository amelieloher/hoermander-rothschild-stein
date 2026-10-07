-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H2.KernelDifferenceIntegral
public import RothschildStein.H2.CancellationIntegral

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set MeasureTheory Metric
open scoped ENNReal

namespace RothschildStein.H2
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]

/-- The cancelled bad-piece integral has the precise L¹ tail
constant S*c₅(β)*4⁻ᵝ (BB p. 320, transposed kernel bound with the adjusted radius). -/
theorem LocDoubling.cancelled_bad_integral (D : LocDoubling X)
    {xbar z : X} {R r β A S : ℝ} {K : X → X → ℝ}
    (hKt : KernelClass D.μ D.Ω₁ β 0 A S (fun x y => K y x))
    (hk : Measurable (Function.uncurry K))
    (hU : ball xbar R ⊆ D.Ω₁) (hR : R < D.κ)
    (hz : z ∈ D.Ω₁) (hB : ball z r ⊆ D.Ω₁)
    (hr : 0 < r) (hcap : 5 * r ≤ D.κ)
    (hsupport : ∀ a b, a ∉ ball xbar R ∨ b ∉ ball xbar R → K a b = 0)
    (b : X → ℝ) (hb : Measurable b) :
    (∫⁻ y in ball xbar R \ ball z (4 * r),
      ‖∫ x in ball z r, (K y x - K y z) * b x ∂D.μ‖ₑ ∂D.μ) ≤
      ENNReal.ofReal (S * volumeIntegralConstant D.C_D β * (4 : ℝ) ^ (-β)) *
        ∫⁻ x in D.Ω₂, ‖b x‖ₑ ∂D.μ := by
  have hBm : MeasurableSet (ball z r) := isOpen_ball.measurableSet
  have hYm : MeasurableSet (ball xbar R \ ball z (4 * r)) :=
    isOpen_ball.measurableSet.diff isOpen_ball.measurableSet
  have hμB : D.μ (ball z r) ≠ ∞ :=
    (D.outerPatch.doubling z hz r hr (by change r ≤ 6 * D.κ; linarith [D.κ_pos])).2.1.ne
  have hμY : D.μ (ball xbar R \ ball z (4 * r)) ≠ ∞ :=
    ne_of_lt ((measure_mono (sdiff_subset.trans (hU.trans D.sub₁₂))).trans_lt D.finΩ₂)
  have hdiff : Measurable (fun p : X × X => K p.1 p.2 - K p.1 z) :=
    hk.sub (hk.comp (measurable_fst.prodMk (measurable_const (a := z))))
  have htail : ∀ x ∈ ball z r,
      (∫⁻ y in ball xbar R \ ball z (4 * r), ‖K y x - K y z‖ₑ ∂D.μ) ≤
        ENNReal.ofReal (S * volumeIntegralConstant D.C_D β * (4 : ℝ) ^ (-β)) := by
    intro x hx
    exact D.kernel_difference_integral hKt hU hR hz (hB hx) hr hcap
      (by simpa only [mem_ball, dist_comm] using hx) hsupport
  exact (cancellation_integral_l1_bound D.μ hBm hYm hμB hμY
    (fun y x => K y x - K y z) hdiff b hb _ htail).trans
    (mul_le_mul' le_rfl (lintegral_mono' (Measure.restrict_mono (hB.trans D.sub₁₂) le_rfl) le_rfl))

end RothschildStein.H2
