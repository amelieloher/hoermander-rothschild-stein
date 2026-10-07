-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H2.SplittingIntegrals
public import RothschildStein.H2.IntegralSubsetBounds

set_option autoImplicit false
set_option relaxedAutoImplicit false

@[expose] public section
noncomputable section
open Set MeasureTheory Metric Filter
open scoped NNReal ENNReal Topology

namespace RothschildStein.H2
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
variable {D : LocDoubling X} {d : TruncDist D}

omit [MeasurableSpace X] [BorelSpace X] in
/-- The cutoff's exponent-one seminorm is at most its Lipschitz constant. -/
theorem KernelCutoff.holderSemi_one_le {U G : Set X} {L : ℝ≥0} {b : X → ℝ}
    (hb : KernelCutoff U L b) : holderSemi 1 G b ≤ ENNReal.ofReal L :=
  holderSemi_le_of_bound L.coe_nonneg (by
    intro x _ y _
    simpa only [NNReal.coe_one, Real.rpow_one, Real.dist_eq] using hb.lipschitz.dist_le_mul x y)

/-- The exponent-one volume constant is exactly twice the doubling constant. -/
theorem volumeIntegralConstant_one (C : ℝ) : volumeIntegralConstant C 1 = 2 * C := by
  norm_num [volumeIntegralConstant, Real.rpow_neg_one]
  ring

/-- (3) Explicit L1 dominant for the regularized singular cutoff term,
BB Proposition 7.17, p. 307. -/
theorem LocalKernelData.singular_b_absolute (Q : LocalKernelData D d) {x : X}
    (hx : x ∈ ball Q.z Q.R) :
    IntegrableOn (fun y => Q.K₀ x y * (Q.b y - Q.b x)) (ball Q.z (2 * Q.R)) D.μ ∧
      (∫⁻ y in ball Q.z (2 * Q.R), ENNReal.ofReal |Q.K₀ x y * (Q.b y - Q.b x)| ∂D.μ) ≤
        ENNReal.ofReal (2 * D.C_D * Q.R * (Q.Lᵦ : ℝ) * Q.A₀) := by
  obtain ⟨hi, hb⟩ := Q.supported_singular.regularized_absolute (δ := 1) (by norm_num)
    Q.cutoff_b.boundedHolder_one hx
  refine ⟨hi, hb.trans ?_⟩
  have hh : (holderSemi 1 (ball Q.z (2 * Q.R)) Q.b).toReal ≤ (Q.Lᵦ : ℝ) := by
    have he := ENNReal.toReal_mono ENNReal.ofReal_ne_top
      (Q.cutoff_b.holderSemi_one_le (G := ball Q.z (2 * Q.R)))
    simpa only [ENNReal.toReal_ofReal Q.Lᵦ.coe_nonneg] using he
  apply ENNReal.ofReal_le_ofReal
  simp only [NNReal.coe_one, zero_add, Real.rpow_one, volumeIntegralConstant_one]
  have he := mul_le_mul_of_nonneg_left hh (mul_nonneg (mul_nonneg Q.singular.A_nonneg
    (by linarith [D.one_lt_C_D] : 0 ≤ 2 * D.C_D)) Q.radius_pos.le)
  nlinarith

/-- (3) Explicit fractional cutoff dominant, BB p. 307. -/
theorem LocalKernelData.fractional_b_absolute (Q : LocalKernelData D d) {x : X}
    (hx : x ∈ ball Q.z Q.R) :
    IntegrableOn (fun y => Q.K₁ x y * Q.b y) (ball Q.z (2 * Q.R)) D.μ ∧
      (∫⁻ y in ball Q.z (2 * Q.R), ENNReal.ofReal |Q.K₁ x y * Q.b y| ∂D.μ) ≤
        ENNReal.ofReal (Q.A₁ * volumeIntegralConstant D.C_D Q.ν * Q.R ^ Q.ν) := by
  simpa only [mul_one] using Q.supported_fractional.fractional_absolute Q.ν_pos
    (Q.cutoff_b.lipschitz.continuous.measurable.aestronglyMeasurable
      (μ := D.μ.restrict (ball Q.z (2 * Q.R)))) (M := 1) (by norm_num) (Q.b_unit_bound _) hx

/-- The exact shell cancellation constant, with Λ_b=R L_b. -/
def LocalKernelData.cancellationConstant (Q : LocalKernelData D d) : ℝ :=
  2 * D.C_D * Q.R * (Q.Lᵦ : ℝ) * Q.A₀ +
    Q.A₁ * volumeIntegralConstant D.C_D Q.ν * Q.R ^ Q.ν

/-- The exact cancellation constant is nonnegative. -/
theorem LocalKernelData.cancellationConstant_nonneg (Q : LocalKernelData D d) :
    0 ≤ Q.cancellationConstant := by
  have hc := (volumeIntegralConstant_pos (C := D.C_D) (by linarith [D.one_lt_C_D]) Q.ν_pos).le
  have hA₀ := Q.singular.A_nonneg
  have hA₁ := Q.fractional.A_nonneg
  have hR := Q.radius_pos.le
  have hCD : 0 ≤ D.C_D := by linarith [D.one_lt_C_D]
  unfold LocalKernelData.cancellationConstant
  positivity

end RothschildStein.H2
