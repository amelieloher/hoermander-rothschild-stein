-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H2.LocalOperatorFullExtension
public import RothschildStein.H2.OperatorPairExtension

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set MeasureTheory Metric
open scoped ENNReal

namespace RothschildStein.H2
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]

/-- The localized Lᵖ extensions satisfy the summed norm bound, agree with the L² operators, and are adjoints on conjugate spaces (BB p. 326). -/
theorem LocDoubling.operator_pair_extension_of_l2_certificate (D : LocDoubling X)
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
    (hp : 1 < p) [Fact (1 ≤ ENNReal.ofReal p)]
    [Fact (1 ≤ ENNReal.ofReal (Real.conjExponent p))] :
    let μ := D.μ.restrict (ball xbar R)
    let C := 2 * nonnegativeWeakConstant D βs Ss cT m
    let Cs := 2 * nonnegativeWeakConstant D β S cT m
    ∃ Tp Tsp : Lp ℝ (ENNReal.ofReal p) μ →L[ℝ] Lp ℝ (ENNReal.ofReal p) μ,
    ∃ Tsq : Lp ℝ (ENNReal.ofReal (Real.conjExponent p)) μ →L[ℝ]
        Lp ℝ (ENNReal.ofReal (Real.conjExponent p)) μ,
      ‖Tp‖ + ‖Tsp‖ ≤ operatorAllExponentConstant C Cs cT p + operatorAllExponentConstant Cs C cT p ∧
      (∀ v : lpL2Intersection μ (ENNReal.ofReal p),
        (fun x => (Tp (v : Lp ℝ (ENNReal.ofReal p) μ)) x) =ᵐ[μ]
          fun x => (T (lpL2ToL2 μ (ENNReal.ofReal p) v)) x) ∧
      (∀ v : lpL2Intersection μ (ENNReal.ofReal p),
        (fun x => (Tsp (v : Lp ℝ (ENNReal.ofReal p) μ)) x) =ᵐ[μ]
          fun x => (Ts (lpL2ToL2 μ (ENNReal.ofReal p) v)) x) ∧
      (∀ w : lpL2Intersection μ (ENNReal.ofReal (Real.conjExponent p)),
        (fun x => (Tsq (w : Lp ℝ (ENNReal.ofReal (Real.conjExponent p)) μ)) x) =ᵐ[μ]
          fun x => (Ts (lpL2ToL2 μ (ENNReal.ofReal (Real.conjExponent p)) w)) x) ∧
      (∀ f : Lp ℝ (ENNReal.ofReal p) μ, ∀ g : Lp ℝ (ENNReal.ofReal (Real.conjExponent p)) μ,
        (∫ x, (Tp f) x * g x ∂μ) = ∫ x, f x * (Tsq g) x ∂μ) := by
  let : IsFiniteMeasure (D.μ.restrict (ball xbar R)) :=
    ⟨by simpa using (measure_mono (hU.trans D.sub₁₂)).trans_lt D.finΩ₂.lt_top⟩
  exact operator_pair_extension_of_weak_one_one (D.μ.restrict (ball xbar R)) T Ts hT.norm_le hTs.norm_le
    (mul_nonneg (by norm_num) (nonnegativeWeakConstant_nonneg D hT.kernel_transpose.β_pos hT.kernel_transpose.S_nonneg))
    (mul_nonneg (by norm_num) (nonnegativeWeakConstant_nonneg D hTs.kernel_transpose.β_pos hTs.kernel_transpose.S_nonneg))
    hadj
    (fun v t ht => D.operator_weak_one_one_of_volume_lower hxbar T hT.norm_le hT.offDiagonal
      hT.kernel_transpose hT.measurable_kernel hU hR hT.support hm hml v ht)
    (fun v t ht => D.operator_weak_one_one_of_volume_lower hxbar Ts hTs.norm_le hTs.offDiagonal
      hTs.kernel_transpose hTs.measurable_kernel hU hR hTs.support hm hml v ht)
    hp

end RothschildStein.H2
