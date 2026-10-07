-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H3.MomentIntegrability

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public section
noncomputable section
namespace RothschildStein.H3
open MeasureTheory

/-- Probability averaging of a jointly measurable family of
 measure-preserving transports does not increase the spatial pth moment.
 Both joint and output moment integrability are proved. -/
theorem transport_average_moment_bound {α X : Type*}
    [MeasurableSpace α] [MeasurableSpace X]
    (μ : Measure α) [IsProbabilityMeasure μ] (ν : Measure X) [SFinite ν]
    (T : α × X → X) (hT : Measurable T)
    (hpres : ∀ t, MeasurePreserving (fun x => T (t,x)) ν ν)
    {p : ℝ} (hp : 1 ≤ p) {f : X → ℝ} (hf : StronglyMeasurable f)
    (hm : Integrable (fun x => |f x| ^ p) ν) :
    Integrable (fun x => |∫ t, f (T (t,x)) ∂μ| ^ p) ν ∧
      (∫ x, |∫ t, f (T (t,x)) ∂μ| ^ p ∂ν) ≤ ∫ x, |f x| ^ p ∂ν := by
  have hp0 : 0 ≤ p := (by norm_num : (0 : ℝ) ≤ 1).trans hp
  have hfm : StronglyMeasurable (fun x => |f x| ^ p) :=
    (continuous_abs.rpow_const (fun _ => Or.inr hp0)).comp_stronglyMeasurable hf
  have hj : StronglyMeasurable (fun z => f (T z)) := hf.comp_measurable hT
  have hjp : StronglyMeasurable (fun z => |f (T z)| ^ p) :=
    hfm.comp_measurable hT
  have hsection : ∀ t, Integrable (fun x => |f (T (t,x))| ^ p) ν :=
    fun t => (hpres t).integrable_comp_of_integrable hm
  have heq : ∀ t, (∫ x, |f (T (t,x))| ^ p ∂ν) = ∫ x, |f x| ^ p ∂ν := by
    intro t
    have hi := integral_map_of_stronglyMeasurable (μ := ν) (hpres t).measurable hfm
    rw [(hpres t).map_eq] at hi
    exact hi.symm
  have hnorm : ∀ t, (∫ x, ‖|f (T (t,x))| ^ p‖ ∂ν) = ∫ x, |f x| ^ p ∂ν := by
    intro t
    simpa only [Real.norm_eq_abs,abs_of_nonneg (Real.rpow_nonneg (abs_nonneg _) _)]
      using heq t
  have hji : Integrable (fun z => |f (T z)| ^ p) (μ.prod ν) := by
    apply (integrable_prod_iff hjp.aestronglyMeasurable).mpr
    refine ⟨Filter.Eventually.of_forall hsection,?_⟩
    simpa only [hnorm] using (integrable_const (∫ x, |f x| ^ p ∂ν) :
      Integrable (fun _ : α => ∫ x, |f x| ^ p ∂ν) μ)
  obtain ⟨hi,hb⟩ := probability_average_moment_bound_of_moment μ ν hp
    hj.aestronglyMeasurable hji
  refine ⟨hi,hb.trans_eq ?_⟩
  rw [integral_prod _ hji]
  simp only [heq,integral_const,probReal_univ,one_smul]

end RothschildStein.H3
