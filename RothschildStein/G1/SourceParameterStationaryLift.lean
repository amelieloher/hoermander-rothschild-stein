-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.G1.SourceParameterActualDerivative
public import Mathlib.Analysis.Normed.Operator.Prod

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set

namespace RothschildStein.G1

/-- Adjoining stationary coefficient coordinates identifies the
actual full state derivative with the inclusion of the original derivative. -/
theorem stationaryLift_fderiv_eq {A E : Type*}
    [NormedAddCommGroup A] [NormedSpace ℝ A]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    {W : A × E → E} {x : A × E} (hW : DifferentiableAt ℝ W x) :
    fderiv ℝ (fun q => ((0 : A), W q)) x =
      (ContinuousLinearMap.inr ℝ A E).comp (fderiv ℝ W x) := by
  exact ((ContinuousLinearMap.inr ℝ A E).hasFDerivAt.comp x hW.hasFDerivAt).fderiv

/-- The stationary lift does not increase the actual first
coefficient-derivative bound in the product norm. -/
theorem stationaryLift_fderiv_norm_le {A E : Type*}
    [NormedAddCommGroup A] [NormedSpace ℝ A]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    {W : A × E → E} {x : A × E} (hW : DifferentiableAt ℝ W x) :
    ‖fderiv ℝ (fun q => ((0 : A), W q)) x‖ ≤ ‖fderiv ℝ W x‖ := by
  rw [stationaryLift_fderiv_eq hW]
  exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
    (mul_le_of_le_one_left (norm_nonneg _)
      (ContinuousLinearMap.norm_inr_le_one (𝕜 := ℝ) (E := A) (F := E)))

/-- Continuous external dependence of the actual coefficient
state derivatives persists under the stationary lift (BB p. 452). -/
theorem stationaryLift_fderiv_continuousOn {P A E : Type*}
    [TopologicalSpace P] [NormedAddCommGroup A] [NormedSpace ℝ A]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    {U : Set P} {S : Set (A × E)} (W : P → A × E → E)
    (hW : ∀ p ∈ U, ∀ x ∈ S, DifferentiableAt ℝ (W p) x)
    (hD : ContinuousOn (fun q : P × (A × E) => fderiv ℝ (W q.1) q.2) (U ×ˢ S)) :
    ContinuousOn
      (fun q : P × (A × E) => fderiv ℝ (fun x => ((0 : A), W q.1 x)) q.2)
      (U ×ˢ S) := by
  have hc := (ContinuousLinearMap.compL ℝ (A × E) E (A × E)
    (ContinuousLinearMap.inr ℝ A E)).continuous.comp_continuousOn hD
  apply hc.congr
  intro q hq
  exact stationaryLift_fderiv_eq (hW q.1 hq.1 q.2 hq.2)

end RothschildStein.G1
