-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H2.OffDiagonalCancellation
public import RothschildStein.H2.CancelledBadIntegral

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set MeasureTheory Metric
open scoped ENNReal Classical

namespace RothschildStein.H2
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]

/-- The operator applied to a cancelled bad piece has the
uniform off-diagonal L¹ tail (BB p. 320). -/
theorem OffDiagonalL2.bad_piece_l1_tail (D : LocDoubling X)
    {xbar z : X} {R r β A S : ℝ} {K : X → X → ℝ}
    {T : Lp ℝ 2 (D.μ.restrict (ball xbar R)) →L[ℝ]
      Lp ℝ 2 (D.μ.restrict (ball xbar R))}
    (hos : OffDiagonalL2 D (ball xbar R) K T)
    (hKt : KernelClass D.μ D.Ω₁ β 0 A S (fun x y => K y x))
    (hk : Measurable (Function.uncurry K))
    (hU : ball xbar R ⊆ D.Ω₁) (hR : R < D.κ)
    (hz : z ∈ D.Ω₁) (hB : ball z r ⊆ D.Ω₁)
    (hr : 0 < r) (hcap : 5 * r ≤ D.κ)
    (hsupport : ∀ a b, a ∉ ball xbar R ∨ b ∉ ball xbar R → K a b = 0)
    (b : X → ℝ) (hbmeas : Measurable b) (hb : IntegrableOn b D.Ω₂ D.μ)
    (hbU : MemLp b 2 (D.μ.restrict (ball xbar R)))
    (hbzero : ∀ x, x ∉ ball z r → b x = 0)
    (hcancel : (∫ x in D.Ω₂, b x ∂D.μ) = 0) :
    (∫⁻ y in ball xbar R \ ball z (4 * r), ‖(T (hbU.toLp b)) y‖ₑ ∂D.μ) ≤
      ENNReal.ofReal (S * volumeIntegralConstant D.C_D β * (4 : ℝ) ^ (-β)) *
        ∫⁻ x in D.Ω₂, ‖b x‖ₑ ∂D.μ := by
  have hu : MeasurableSet (ball xbar R) := isOpen_ball.measurableSet
  have hb4 : MeasurableSet (ball z (4 * r)) := isOpen_ball.measurableSet
  have heq := hos.cancelled_representation D hu (hU.trans D.sub₁₂) hsupport hz hr
    (by linarith : r ≤ D.κ / 5) (hB.trans D.sub₁₂) b hb hbU hbzero hcancel
  have heqY : ∀ᵐ y ∂D.μ.restrict (ball xbar R \ ball z (4 * r)),
      (T (hbU.toLp b)) y = ∫ x in ball z r, (K y x - K y z) * b x ∂D.μ := by
    filter_upwards [ae_restrict_of_ae_restrict_of_subset sdiff_subset heq,
      ae_restrict_mem (hu.diff hb4)] with y hy hys
    exact hy hys.2
  have henorm : (fun y => ‖(T (hbU.toLp b)) y‖ₑ) =ᵐ[D.μ.restrict (ball xbar R \ ball z (4 * r))]
      (fun y => ‖∫ x in ball z r, (K y x - K y z) * b x ∂D.μ‖ₑ) := by
    filter_upwards [heqY] with y hy
    rw [hy]
  exact (le_of_eq (lintegral_congr_ae henorm)).trans
    (D.cancelled_bad_integral hKt hk hU hR hz hB hr hcap hsupport b hbmeas)

end RothschildStein.H2
