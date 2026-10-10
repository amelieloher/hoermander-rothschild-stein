-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Kernel.LocallyIntegrableL2Curves
public import HeatKernel.Kernel.GlobalHorizontalHeatOperators
public import HeatKernel.Kernel.CoordinateMeasure

/-! # Joint spacetime representatives of the horizontal heat semigroup -/

@[expose] public section
noncomputable section
open MeasureTheory Set TopologicalSpace RothschildStein
namespace HeatKernel

/-- Horizontal heat orbits have jointly measurable, locally integrable coordinate
representatives with the prescribed L² section at every time. -/
theorem exists_globalHorizontalHeat_spacetime_representative {n q : ℕ}
    (G : HomogeneousGroup n) (hq : q ≤ n) :
    ∃ U : Lp ℝ 2 (volume : Measure (Fin n → ℝ)) → (Fin (1 + n) → ℝ) → ℝ,
      (∀ f, Measurable (U f)) ∧
      (∀ f, LocallyIntegrableOn (U f) {z | 0 < z 0} volume) ∧
      ∀ f t, (fun x => U f ((timeSpaceCoordinates n).symm (t, x))) =ᵐ[volume]
        globalHorizontalHeatOperator G hq t.toNNReal f := by
  have hbound (f : Lp ℝ 2 (volume : Measure (Fin n → ℝ))) (t : ℝ) :
      ‖globalHorizontalHeatOperator G hq t.toNNReal f‖ ≤ ‖f‖ := by
    simpa only [one_mul] using
      (globalHorizontalHeatOperator G hq t.toNNReal).le_of_opNorm_le
        (norm_globalHorizontalHeatOperator_le_one G hq t.toNNReal) f
  have hex (f : Lp ℝ 2 (volume : Measure (Fin n → ℝ))) :=
    exists_locallyIntegrable_joint_L2_representative
      (fun t : ℝ => globalHorizontalHeatOperator G hq t.toNNReal f)
      ((continuous_globalHorizontalHeatOperator_apply G hq f).comp continuous_real_toNNReal)
      ‖f‖ (hbound f)
  choose u hu hint hslice using hex
  let U := fun f z => u f (timeSpaceCoordinates n z)
  refine ⟨U, ?_, ?_, ?_⟩
  · intro f
    exact (hu f).comp (timeSpaceCoordinates n).toHomeomorph.measurable
  · intro f
    have hpre : timeSpaceCoordinates n ⁻¹' {z : ℝ × (Fin n → ℝ) | 0 < z.1} =
        {z | 0 < z 0} := by
      ext z
      simp only [mem_preimage, mem_ofPred_eq, timeSpaceCoordinates_fst]
    simpa only [U, Function.comp_def, hpre] using
      locallyIntegrableOn_comp_timeSpaceCoordinates n
        (isOpen_lt continuous_const continuous_fst) (hint f)
  · intro f t
    simpa only [U, ContinuousLinearEquiv.apply_symm_apply] using hslice f t

end HeatKernel
