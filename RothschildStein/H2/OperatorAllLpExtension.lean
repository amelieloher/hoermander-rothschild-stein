-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H2.OperatorConstantBounds
public import RothschildStein.H2.OperatorLpExtension

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set MeasureTheory
open scoped ENNReal

namespace RothschildStein.H2
variable {X : Type*} [MeasurableSpace X]

/-- Bounded extension for every finite p > 1, under
exact weak endpoints and L² adjointness (BB p. 326). -/
theorem operator_all_lp_extension_of_weak_one_one (μ : Measure X) [IsFiniteMeasure μ]
    (T Ts : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ) {cT C Cs p : ℝ}
    (hcT : ‖T‖ ≤ cT) (hcTs : ‖Ts‖ ≤ cT) (hC : 0 ≤ C) (hCs : 0 ≤ Cs)
    (hadj : ∀ v w : Lp ℝ 2 μ, (∫ x, (T v) x * w x ∂μ) = ∫ x, v x * (Ts w) x ∂μ)
    (hweak : ∀ v : Lp ℝ 2 μ, ∀ t : ℝ, 0 < t →
      distribution μ (fun x => (T v) x) t ≤ ENNReal.ofReal (C / t) * eLpNorm v 1 μ)
    (hweaks : ∀ v : Lp ℝ 2 μ, ∀ t : ℝ, 0 < t →
      distribution μ (fun x => (Ts v) x) t ≤ ENNReal.ofReal (Cs / t) * eLpNorm v 1 μ)
    (hp : 1 < p) [Fact (1 ≤ ENNReal.ofReal p)] :
    ∃ Tp : Lp ℝ (ENNReal.ofReal p) μ →L[ℝ] Lp ℝ (ENNReal.ofReal p) μ,
      ‖Tp‖ ≤ operatorAllExponentConstant C Cs cT p ∧
      (∀ v : lpL2Intersection μ (ENNReal.ofReal p),
        (fun x => (Tp (v : Lp ℝ (ENNReal.ofReal p) μ)) x) =ᵐ[μ]
          fun x => (T (lpL2ToL2 μ (ENNReal.ofReal p) v)) x) := by
  exact operator_lp_extension_of_bound μ (ENNReal.ofReal p) ENNReal.ofReal_ne_top T
    (operatorAllExponentConstant_nonneg hC hCs ((norm_nonneg T).trans hcT) hp)
    (fun v hvp => operator_lp_all_of_weak_one_one μ T Ts hcT hcTs hC hCs hadj hweak hweaks hp v hvp)

end RothschildStein.H2
