-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H2.OperatorAllLpExtension
public import RothschildStein.H2.OperatorExtensionAdjoint

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set MeasureTheory
open scoped ENNReal

namespace RothschildStein.H2
variable {X : Type*} [MeasurableSpace X]

/-- Both bounded extensions, their summed explicit norm bound,
L² consistency, and full conjugate-space adjointness. Endpoint hypotheses
follow from the weak endpoint and L² adjointness bounds (BB p. 326). -/
theorem operator_pair_extension_of_weak_one_one (μ : Measure X) [IsFiniteMeasure μ]
    (T Ts : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ) {cT C Cs p : ℝ}
    (hcT : ‖T‖ ≤ cT) (hcTs : ‖Ts‖ ≤ cT) (hC : 0 ≤ C) (hCs : 0 ≤ Cs)
    (hadj : ∀ v w : Lp ℝ 2 μ, (∫ x, (T v) x * w x ∂μ) = ∫ x, v x * (Ts w) x ∂μ)
    (hweak : ∀ v : Lp ℝ 2 μ, ∀ t : ℝ, 0 < t →
      distribution μ (fun x => (T v) x) t ≤ ENNReal.ofReal (C / t) * eLpNorm v 1 μ)
    (hweaks : ∀ v : Lp ℝ 2 μ, ∀ t : ℝ, 0 < t →
      distribution μ (fun x => (Ts v) x) t ≤ ENNReal.ofReal (Cs / t) * eLpNorm v 1 μ)
    (hp : 1 < p) [Fact (1 ≤ ENNReal.ofReal p)]
    [Fact (1 ≤ ENNReal.ofReal (Real.conjExponent p))] :
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
  have hadjs : ∀ v w : Lp ℝ 2 μ, (∫ x, (Ts v) x * w x ∂μ) = ∫ x, v x * (T w) x ∂μ := by
    intro v w
    simpa only [mul_comm] using (hadj w v).symm
  obtain ⟨Tp, hnorm, hlink⟩ := operator_all_lp_extension_of_weak_one_one μ T Ts hcT hcTs hC hCs hadj hweak hweaks hp
  obtain ⟨Tsp, hnorms, hlinks⟩ := operator_all_lp_extension_of_weak_one_one μ Ts T hcTs hcT hCs hC hadjs hweaks hweak hp
  have hpq := Real.HolderConjugate.conjExponent hp
  obtain ⟨Tsq, _, hlinkq⟩ := operator_all_lp_extension_of_weak_one_one μ Ts T hcTs hcT hCs hC hadjs hweaks hweak hpq.symm.lt
  exact ⟨Tp, Tsp, Tsq, add_le_add hnorm hnorms, hlink, hlinks, hlinkq,
    operator_extensions_adjoint μ hpq T Ts Tp Tsq hadj hlink hlinkq⟩

end RothschildStein.H2
