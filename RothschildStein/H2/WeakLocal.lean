-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H2.WeakSupported

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set MeasureTheory Metric
open scoped ENNReal

namespace RothschildStein.H2
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]

/-- Weak (1,1) on the actual local L² space. Kernel and
operator hypotheses are precisely the off-diagonal and transposed smoothness bounds (BB pp. 319–320). -/
theorem LocDoubling.operator_weak_one_one_of_volume_lower (D : LocDoubling X)
    {xbar : X} {R β A S cT m : ℝ} {K : X → X → ℝ}
    (hxbar : xbar ∈ D.Ω₀)
    (T : Lp ℝ 2 (D.μ.restrict (ball xbar R)) →L[ℝ]
      Lp ℝ 2 (D.μ.restrict (ball xbar R)))
    (hcT : ‖T‖ ≤ cT)
    (hos : OffDiagonalL2 D (ball xbar R) K T)
    (hKt : KernelClass D.μ D.Ω₁ β 0 A S (fun x y => K y x))
    (hk : Measurable (Function.uncurry K))
    (hU : ball xbar R ⊆ D.Ω₁) (hR : R < D.κ)
    (hsupport : ∀ a b, a ∉ ball xbar R ∨ b ∉ ball xbar R → K a b = 0)
    (hm : 0 < m) (hml : ∀ z ∈ D.Ω₁, ENNReal.ofReal m ≤ D.μ (ball z D.κ))
    (v : Lp ℝ 2 (D.μ.restrict (ball xbar R))) {α : ℝ} (hα : 0 < α) :
    distribution (D.μ.restrict (ball xbar R)) (fun x => (T v) x) α ≤
      ENNReal.ofReal (2 * nonnegativeWeakConstant D β S cT m / α) *
        eLpNorm v 1 (D.μ.restrict (ball xbar R)) := by
  let U := ball xbar R
  have hUm : MeasurableSet U := isOpen_ball.measurableSet
  have hU₂ : U ⊆ D.Ω₂ := hU.trans D.sub₁₂
  let f : X → ℝ := U.indicator (fun x => v x)
  have hf : MemLp f 2 (D.μ.restrict D.Ω₂) := by
    apply (memLp_indicator_iff_restrict hUm).mpr
    rw [Measure.restrict_restrict_of_subset hU₂]
    exact Lp.memLp v
  have hfs : ∀ᵐ x ∂D.μ.restrict D.Ω₂, x ∉ ball xbar D.κ → f x = 0 :=
    Filter.Eventually.of_forall fun x hx => indicator_of_notMem
      (fun hu => hx (ball_subset_ball hR.le hu)) _
  have hn : eLpNorm f 1 (D.μ.restrict D.Ω₂) = eLpNorm v 1 (D.μ.restrict U) := by
    rw [eLpNorm_indicator_eq_eLpNorm_restrict hUm, Measure.restrict_restrict_of_subset hU₂]
  have hν := Measure.restrict_mono hU₂ (le_rfl : D.μ ≤ D.μ)
  have heq : (hf.mono_measure hν).toLp f = v := by
    apply Lp.ext
    filter_upwards [(hf.mono_measure hν).coeFn_toLp, ae_restrict_mem hUm] with x hx hxU
    rw [hx]
    exact indicator_of_mem hxU _
  have hw := D.operator_weak_supported hxbar T hcT hos hKt hk hU hR hsupport hm hml f hf hfs hα
  rwa [heq, hn] at hw

end RothschildStein.H2
