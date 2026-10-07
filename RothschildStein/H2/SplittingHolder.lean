-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H2.SplittingHolderData

set_option autoImplicit false
set_option relaxedAutoImplicit false

@[expose] public section
noncomputable section
open Set MeasureTheory Metric Filter
open scoped NNReal ENNReal Topology

namespace RothschildStein.H2
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
variable {D : LocDoubling X} {d : TruncDist D}

/-- T(1) has the explicit Hölder norm bound on the cutoff ball.
BB Proposition 7.17, pp. 307–308, under the stated support and size hypotheses. -/
theorem LocalKernelData.one_holder_norm_le (Q : LocalKernelData D d) {γ : ℝ≥0}
    (hγ : 0 < γ) (hγ₀ : (γ : ℝ) < Q.β₀) (hγβ : (γ : ℝ) ≤ Q.β) (hγν : (γ : ℝ) < Q.ν) :
    boundedHolderNorm γ (ball Q.z Q.R) Q.oneLimit ≤ ENNReal.ofReal (Q.oneHolderConstant γ) := by
  have hγr : 0 < (γ : ℝ) := hγ
  have hγ₁ : γ ≤ 1 := by exact_mod_cast hγ₀.le.trans Q.singular.β_le_one
  have hθ₁ := d.θ₁_pos.le
  have hθ₂ := (d.θ₁_pos.trans_le d.θ₁_le).le
  have hCD : 0 < D.C_D := by linarith [D.one_lt_C_D]
  have hcγ := (volumeIntegralConstant_pos (C := D.C_D) hCD hγr).le
  have hcr := regularizedHolderConstant_nonneg hCD hγr hγ₀ hθ₁ hθ₂
  let B : ℝ := regularizedHolderConstant Q.β₀ γ D.C_D d.θ₁ d.θ₂ * (Q.A₀ + Q.S₀) +
    volumeIntegralConstant D.C_D γ * Q.A₀ * Q.R ^ (γ : ℝ)
  let LB : ℝ := (Q.Lᵦ : ℝ) * (4 * Q.R) ^ (1 - (γ : ℝ))
  let LA : ℝ := 1 + (Q.Lₐ : ℝ) * (2 * Q.R) ^ (1 - (γ : ℝ))
  have hB : 0 ≤ B := by
    dsimp [B]
    exact add_nonneg (mul_nonneg hcr (add_nonneg Q.singular.A_nonneg Q.singular.S_nonneg))
      (mul_nonneg (mul_nonneg hcγ Q.singular.A_nonneg) (Real.rpow_nonneg Q.radius_pos.le _))
  have hR := Q.radius_pos.le
  have hLB : 0 ≤ LB := by dsimp [LB]; positivity
  have hLA : 0 ≤ LA := by dsimp [LA]; positivity
  have hBγ := Q.cutoff_b.boundedHolder_ball (z := Q.z) (r := 2 * Q.R) (by linarith [Q.radius_pos]) hγ₁
  have hr := Q.supported_singular.regularized_holder_norm_le d Q.singular_shellCancellation hγ hγ₀ hBγ
  have hsB : holderSemi γ (ball Q.z (2 * Q.R)) Q.b ≤ ENNReal.ofReal LB := by
    simpa only [show 2 * (2 * Q.R) = 4 * Q.R by ring] using
      Q.cutoff_b.holderSemi_ball_le (z := Q.z) (r := 2 * Q.R) (by linarith [Q.radius_pos]) hγ₁
  have hrB : boundedHolderNorm γ (ball Q.z Q.R)
      (regularizedIntegral D.μ (ball Q.z (2 * Q.R)) Q.K₀ Q.b) ≤ ENNReal.ofReal B * ENNReal.ofReal LB := by
    have hr' : boundedHolderNorm γ (ball Q.z Q.R)
        (regularizedIntegral D.μ (ball Q.z (2 * Q.R)) Q.K₀ Q.b) ≤ ENNReal.ofReal B * holderSemi γ (ball Q.z (2 * Q.R)) Q.b := by
      simpa only [B, add_zero] using hr
    exact hr'.trans (mul_le_mul_right hsB _)
  have haN : boundedHolderNorm γ (ball Q.z Q.R) Q.a ≤ ENNReal.ofReal LA :=
    Q.cutoff_a.holderNorm_ball_le Q.radius_pos hγ₁
  have haγ := Q.cutoff_a.boundedHolder_ball (z := Q.z) Q.radius_pos hγ₁
  have hrγ := Q.supported_singular.regularized_boundedHolder d Q.singular_shellCancellation hγ hγ₀ hBγ
  have hp := (boundedHolderNorm_mul_le haγ hrγ).trans (mul_le_mul haN hrB (by exact bot_le) (by exact bot_le))
  let K₁ := localizedKernel (ball Q.z Q.R) Q.a Q.b Q.K₁
  have hf₁ := Q.supported_localized_fractional.fractional_holder_norm_le hγ hγβ hγν
    (f := fun _ => 1) aestronglyMeasurable_const (M := 1) (by norm_num)
    (ae_of_all _ (by intro y; norm_num))
  simp only [mul_one] at hf₁
  have hCf : 0 ≤ fractionalHolderConstant D.C_D D.κ (2 * Q.R) γ Q.ν * (Q.A₁ + Q.fractionalS) := by
    have hsemi := fractionalSemiConstant_nonneg (R := 2 * Q.R) hCD D.κ_pos (by linarith [Q.radius_pos]) Q.ν_pos hγν
    have hcf : 0 ≤ fractionalHolderConstant D.C_D D.κ (2 * Q.R) γ Q.ν := by
      unfold fractionalHolderConstant
      exact add_nonneg hsemi (mul_nonneg (volumeIntegralConstant_pos hCD Q.ν_pos).le
        (Real.rpow_nonneg (by linarith [Q.radius_pos]) _))
    exact mul_nonneg hcf (add_nonneg Q.fractional.A_nonneg Q.supported_localized_fractional.kernel.S_nonneg)
  have heq : EqOn Q.oneLimit
      (fun x => Q.a x * regularizedIntegral D.μ (ball Q.z (2 * Q.R)) Q.K₀ Q.b x +
        fractionalIntegral D.μ (ball Q.z Q.R) K₁ (fun _ => 1) x) (ball Q.z Q.R) := by
    intro x hx
    have he := Q.localized_integral_eq hx MeasurableSet.univ Q.K₁
    have he' : fractionalIntegral D.μ (ball Q.z Q.R) K₁ (fun _ => 1) x =
        Q.a x * fractionalIntegral D.μ (ball Q.z (2 * Q.R)) Q.K₁ Q.b x := by
      simpa only [fractionalIntegral, mul_one, inter_univ] using he
    dsimp only
    rw [he']
    unfold LocalKernelData.oneLimit
    ring
  rw [boundedHolderNorm_congr heq]
  have hsum := boundedHolderNorm_add_le (δ := γ) (G := ball Q.z Q.R)
    (f := fun x => Q.a x * regularizedIntegral D.μ (ball Q.z (2 * Q.R)) Q.K₀ Q.b x)
    (g := fractionalIntegral D.μ (ball Q.z Q.R) K₁ (fun _ => 1))
  calc
    _ ≤ _ := hsum
    _ ≤ ENNReal.ofReal LA * (ENNReal.ofReal B * ENNReal.ofReal LB) +
        ENNReal.ofReal (fractionalHolderConstant D.C_D D.κ (2 * Q.R) γ Q.ν * (Q.A₁ + Q.fractionalS)) := add_le_add hp hf₁
    _ = _ := by
      rw [← ENNReal.ofReal_mul hB, ← ENNReal.ofReal_mul hLA,
        ← ENNReal.ofReal_add (mul_nonneg hLA (mul_nonneg hB hLB)) hCf]
      congr 1
      change LA * (B * LB) + _ = LA * LB * B + _
      ring

/-- T(1) belongs to the bounded Hölder space. -/
theorem LocalKernelData.one_boundedHolder (Q : LocalKernelData D d) {γ : ℝ≥0}
    (hγ : 0 < γ) (hγ₀ : (γ : ℝ) < Q.β₀) (hγβ : (γ : ℝ) ≤ Q.β) (hγν : (γ : ℝ) < Q.ν) :
    BoundedHolder γ (ball Q.z Q.R) Q.oneLimit :=
  (Q.one_holder_norm_le hγ hγ₀ hγβ hγν).trans_lt ENNReal.ofReal_lt_top

end RothschildStein.H2
