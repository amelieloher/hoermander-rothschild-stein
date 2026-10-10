-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Form.SmoothCoreGenerator
public import HeatKernel.Form.GroupCutoffCovariance
public import RothschildStein.G2.InvariantDivergence
import Mathlib.Tactic.Linter

/-! # The horizontal sum of squares on the smooth compact core -/

@[expose] public section

noncomputable section

open Set MeasureTheory TopologicalSpace RothschildStein RothschildStein.G2

namespace HeatKernel

/-- The positive horizontal form operator on a homogeneous group is the negative sum of
squared invariant fields on smooth compact functions; the heat generator has the opposite sign. -/
theorem exists_horizontal_core_operatorValue {N q : ℕ} (G : HomogeneousGroup N)
    (hq : q ≤ N) {f : (Fin N → ℝ) → ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hc : HasCompactSupport f) :
    ∃ u : energyGraph (N := N) ⊤ (G.horizontalFields hq), ∃ g : SpatialL2 (N := N) ⊤,
      ((u : GradientSpace (N := N) ⊤ q).fst =ᵐ[volume] f) ∧
      (g =ᵐ[volume] (fun x => -(∑ i, fieldDerivative (G.horizontalFields hq i)
        (fieldDerivative (G.horizontalFields hq i) f) x))) ∧
      IsWeakFormOperatorValue (energyInclusion ⊤ (G.horizontalFields hq))
        (horizontalEnergy ⊤ (G.horizontalFields hq)) u g := by
  have hX : ∀ i : Fin q, ContDiff ℝ (⊤ : ℕ∞) (G.horizontalFields hq i) := by
    intro i
    simpa only [HomogeneousGroup.horizontalFields, canonicalField_eq_leftField] using
      contDiff_leftField G (Hormander.Interface.basisVec (Fin.castLE hq i))
  apply exists_smooth_core_operatorValue (G.horizontalFields hq) hX ?_ hf hc
  intro i φ hφ x
  simpa only [HomogeneousGroup.horizontalFields, canonicalField_eq_leftField] using
    leftField_transpose G (Hormander.Interface.basisVec (Fin.castLE hq i)) φ hφ x



end HeatKernel
