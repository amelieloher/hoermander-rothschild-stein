-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H2.WeakNonnegative
public import RothschildStein.H2.WeakSigned

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set MeasureTheory Metric
open scoped ENNReal

namespace RothschildStein.H2
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]

/-- Weak (1,1) for signed inputs supported in the chart, with
the explicit factor two (BB pp. 319–320). -/
theorem LocDoubling.operator_weak_supported (D : LocDoubling X)
    {xbar : X} {R β A S α cT m : ℝ} {K : X → X → ℝ}
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
    (f : X → ℝ) (hf : MemLp f 2 (D.μ.restrict D.Ω₂))
    (hfs : ∀ᵐ x ∂D.μ.restrict D.Ω₂, x ∉ ball xbar D.κ → f x = 0)
    (hα : 0 < α) :
    distribution (D.μ.restrict (ball xbar R))
      (fun x => (T ((hf.mono_measure (Measure.restrict_mono (hU.trans D.sub₁₂) le_rfl)).toLp f)) x) α ≤
        ENNReal.ofReal (2 * nonnegativeWeakConstant D β S cT m / α) *
          eLpNorm f 1 (D.μ.restrict D.Ω₂) := by
  let : IsFiniteMeasure (D.μ.restrict D.Ω₂) := ⟨by simpa using D.finΩ₂⟩
  apply operator_weak_signed_of_nonnegative (D.μ.restrict D.Ω₂)
    (D.μ.restrict (ball xbar R)) (Measure.restrict_mono (hU.trans D.sub₁₂) le_rfl)
    T (ball xbar D.κ) (nonnegativeWeakConstant D β S cT m) ?_ f hf hfs hα
  intro v hv hn hs t ht
  obtain ⟨hvU, hweak⟩ := D.operator_weak_nonnegative hxbar T hcT ht hos hKt hk hU hR
    hsupport hm hml v hv (hv.integrable (by norm_num : (1 : ℝ≥0∞) ≤ 2)) hn hs
  exact hweak

end RothschildStein.H2
