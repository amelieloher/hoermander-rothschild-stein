-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H2.WeakCover
public import RothschildStein.H2.FractionalHedberg

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set MeasureTheory Metric
open scoped ENNReal

namespace RothschildStein.H2
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]

/-- The nonnegative weak-type coefficient (BB pp. 319–320). -/
def nonnegativeWeakConstant (D : LocDoubling X) (β S cT m : ℝ) : ℝ :=
  4 * cT ^ 2 * ((D.C_D ^ 7 + D.C_D ^ 5) * goodAverageConstant D m) +
    D.C_D ^ 2 * (D.C_D ^ 7 + D.C_D ^ 5) +
    4 * (S * volumeIntegralConstant D.C_D β * (4 : ℝ) ^ (-β))

/-- Uniform weak type for nonnegative inputs supported in the
local chart, using the good/bad decomposition (BB pp. 319–320). -/
theorem LocDoubling.operator_weak_nonnegative (D : LocDoubling X)
    {xbar : X} {R β A S α cT m : ℝ} {K : X → X → ℝ}
    (hxbar : xbar ∈ D.Ω₀)
    (T : Lp ℝ 2 (D.μ.restrict (ball xbar R)) →L[ℝ]
      Lp ℝ 2 (D.μ.restrict (ball xbar R)))
    (hcT : ‖T‖ ≤ cT) (hα : 0 < α)
    (hos : OffDiagonalL2 D (ball xbar R) K T)
    (hKt : KernelClass D.μ D.Ω₁ β 0 A S (fun x y => K y x))
    (hk : Measurable (Function.uncurry K))
    (hU : ball xbar R ⊆ D.Ω₁) (hR : R < D.κ)
    (hsupport : ∀ a b, a ∉ ball xbar R ∨ b ∉ ball xbar R → K a b = 0)
    (hm : 0 < m) (hml : ∀ z ∈ D.Ω₁, ENNReal.ofReal m ≤ D.μ (ball z D.κ))
    (f : X → ℝ) (hf : MemLp f 2 (D.μ.restrict D.Ω₂))
    (hfi : IntegrableOn f D.Ω₂ D.μ)
    (hn : ∀ᵐ x ∂D.μ.restrict D.Ω₂, 0 ≤ f x)
    (hfs : ∀ᵐ x ∂D.μ.restrict D.Ω₂, x ∉ ball xbar D.κ → f x = 0) :
    ∃ hfU : MemLp f 2 (D.μ.restrict (ball xbar R)),
      distribution (D.μ.restrict (ball xbar R)) (fun x => (T (hfU.toLp f)) x) α ≤
        ENNReal.ofReal (nonnegativeWeakConstant D β S cT m / α) *
          eLpNorm f 1 (D.μ.restrict D.Ω₂) := by
  let N := D.C_D ^ 7 + D.C_D ^ 5
  let C := N * goodAverageConstant D m
  let a := 4 * cT ^ 2 * C
  let b := D.C_D ^ 2 * N
  let c := 4 * (S * volumeIntegralConstant D.C_D β * (4 : ℝ) ^ (-β))
  have hCD : 0 ≤ D.C_D := by linarith [D.one_lt_C_D]
  have hN : 1 ≤ N := by
    dsimp [N]
    have hp := one_le_pow₀ D.one_lt_C_D.le (n := 7)
    have hq := pow_nonneg hCD 5
    linarith
  have hC : 0 ≤ C := mul_nonneg (by linarith)
    ((pow_nonneg hCD 6).trans (le_max_left _ _))
  have ha : 0 ≤ a := mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg cT)) hC
  have hb : 1 ≤ b := by
    have hp : 1 ≤ D.C_D ^ 2 := one_le_pow₀ D.one_lt_C_D.le
    dsimp [b]
    nlinarith
  have hc : 0 ≤ c := mul_nonneg (by norm_num) (mul_nonneg
    (mul_nonneg hKt.S_nonneg (hedbergVolumeIntegralConstant_pos (by linarith [D.one_lt_C_D]) hKt.β_pos).le)
    (Real.rpow_nonneg (by norm_num) _))
  have hconst : nonnegativeWeakConstant D β S cT m = a + b + c := rfl
  have hnorm := eLpNorm_one_eq_lintegral_enorm hf.aestronglyMeasurable
  by_cases hthreshold : eLpNorm f 1 (D.μ.restrict D.Ω₂) / ENNReal.ofReal α < D.μ D.Ω₁
  · obtain ⟨hfU, hw⟩ := D.operator_weak_cover hxbar T hcT hα hos hKt hk hU hR hsupport
      hm hml f hf hfi hn hfs hthreshold
    refine ⟨hfU, hw.trans_eq ?_⟩
    rw [← hnorm, hconst]
    change ENNReal.ofReal (a / α) * eLpNorm f 1 (D.μ.restrict D.Ω₂) +
      (ENNReal.ofReal D.C_D ^ 2 * (ENNReal.ofReal N *
        (eLpNorm f 1 (D.μ.restrict D.Ω₂) / ENNReal.ofReal α)) +
        ENNReal.ofReal (c / α) * eLpNorm f 1 (D.μ.restrict D.Ω₂)) = _
    have hmid : ENNReal.ofReal D.C_D ^ 2 * (ENNReal.ofReal N *
        (eLpNorm f 1 (D.μ.restrict D.Ω₂) / ENNReal.ofReal α)) =
        ENNReal.ofReal (b / α) * eLpNorm f 1 (D.μ.restrict D.Ω₂) := by
      rw [← ENNReal.ofReal_pow hCD, ENNReal.ofReal_div_of_pos hα]
      dsimp [b]
      rw [ENNReal.ofReal_mul (sq_nonneg D.C_D)]
      simp only [div_eq_mul_inv]
      ac_rfl
    rw [hmid, ← add_mul, ← add_mul,
      ← ENNReal.ofReal_add (div_nonneg (by linarith : 0 ≤ b) hα.le) (div_nonneg hc hα.le),
      ← ENNReal.ofReal_add (div_nonneg ha hα.le) (add_nonneg
        (div_nonneg (by linarith : 0 ≤ b) hα.le) (div_nonneg hc hα.le))]
    congr 2
    ring
  · have hfU := hf.mono_measure (Measure.restrict_mono (hU.trans D.sub₁₂) le_rfl)
    refine ⟨hfU, ?_⟩
    calc
      _ ≤ (D.μ.restrict (ball xbar R)) univ := measure_mono (subset_univ _)
      _ = D.μ (ball xbar R) := Measure.restrict_apply_univ _
      _ ≤ D.μ D.Ω₁ := measure_mono hU
      _ ≤ eLpNorm f 1 (D.μ.restrict D.Ω₂) / ENNReal.ofReal α := le_of_not_gt hthreshold
      _ = ENNReal.ofReal (1 / α) * eLpNorm f 1 (D.μ.restrict D.Ω₂) := by
        rw [ENNReal.ofReal_div_of_pos hα, ENNReal.ofReal_one]
        simp only [div_eq_mul_inv, mul_one, mul_comm]
      _ ≤ _ := mul_le_mul' (ENNReal.ofReal_le_ofReal (by rw [hconst]; gcongr; linarith)) le_rfl

end RothschildStein.H2
