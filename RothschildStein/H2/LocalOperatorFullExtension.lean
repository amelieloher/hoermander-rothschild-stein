-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H2.LocalOperatorAllExponents

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set MeasureTheory Metric
open scoped ENNReal

namespace RothschildStein.H2
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]

/-- Full bounded Lᵖ extension with the explicit coefficient,
from the exact two local L² certificates (BB p. 326). -/
theorem LocDoubling.operator_all_lp_extension_of_l2_certificate (D : LocDoubling X)
    {xbar : X} {R β βs A As S Ss cT m p : ℝ} {K : X → X → ℝ}
    (hxbar : xbar ∈ D.Ω₀) (hU : ball xbar R ⊆ D.Ω₁) (hR : R < D.κ)
    (T Ts : Lp ℝ 2 (D.μ.restrict (ball xbar R)) →L[ℝ]
      Lp ℝ 2 (D.μ.restrict (ball xbar R)))
    (hT : LocalL2Certificate D xbar R βs As Ss cT K T)
    (hTs : LocalL2Certificate D xbar R β A S cT (fun x y => K y x) Ts)
    (hadj : ∀ v w : Lp ℝ 2 (D.μ.restrict (ball xbar R)),
      (∫ x, (T v) x * w x ∂D.μ.restrict (ball xbar R)) =
        ∫ x, v x * (Ts w) x ∂D.μ.restrict (ball xbar R))
    (hm : 0 < m) (hml : ∀ z ∈ D.Ω₁, ENNReal.ofReal m ≤ D.μ (ball z D.κ))
    (hp : 1 < p) [Fact (1 ≤ ENNReal.ofReal p)] :
    ∃ Tp : Lp ℝ (ENNReal.ofReal p) (D.μ.restrict (ball xbar R)) →L[ℝ]
        Lp ℝ (ENNReal.ofReal p) (D.μ.restrict (ball xbar R)),
      ‖Tp‖ ≤ operatorAllExponentConstant
        (2 * nonnegativeWeakConstant D βs Ss cT m)
        (2 * nonnegativeWeakConstant D β S cT m) cT p ∧
      (∀ v : lpL2Intersection (D.μ.restrict (ball xbar R)) (ENNReal.ofReal p),
        (fun x => (Tp (v : Lp ℝ (ENNReal.ofReal p) (D.μ.restrict (ball xbar R)))) x)
          =ᵐ[D.μ.restrict (ball xbar R)]
          fun x => (T (lpL2ToL2 (D.μ.restrict (ball xbar R)) (ENNReal.ofReal p) v)) x) := by
  let : IsFiniteMeasure (D.μ.restrict (ball xbar R)) :=
    ⟨by simpa using (measure_mono (hU.trans D.sub₁₂)).trans_lt D.finΩ₂.lt_top⟩
  apply operator_lp_extension_of_bound (D.μ.restrict (ball xbar R)) (ENNReal.ofReal p)
    ENNReal.ofReal_ne_top T
    (operatorAllExponentConstant_nonneg
      (mul_nonneg (by norm_num) (nonnegativeWeakConstant_nonneg D hT.kernel_transpose.β_pos hT.kernel_transpose.S_nonneg))
      (mul_nonneg (by norm_num) (nonnegativeWeakConstant_nonneg D hTs.kernel_transpose.β_pos hTs.kernel_transpose.S_nonneg))
      ((norm_nonneg T).trans hT.norm_le) hp) ?_
  exact fun v hvp => D.operator_lp_all_of_l2_certificate hxbar hU hR T Ts hT hTs hadj hm hml hp v hvp

end RothschildStein.H2
