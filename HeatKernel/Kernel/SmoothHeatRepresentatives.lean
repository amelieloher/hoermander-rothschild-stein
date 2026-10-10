-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Kernel.HeatAdjoint
public import Hormander.Interface
public import Mathlib.MeasureTheory.Measure.OpenPos

/-! # Smooth representatives of weak heat solutions

The spacetime adjoint identity converts a weak heat-test identity into the weak
Hörmander equation. Hypoellipticity and full support give a unique smooth representative.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped BigOperators

namespace HeatKernel

open Hormander.Interface RothschildStein

/-- A locally integrable heat-test solution satisfies the spacetime Hörmander equation. -/
theorem hasWeakHormanderEquation_horizontalHeatFields_of_integral_identity {n q : ℕ}
    (G : HomogeneousGroup n) (hq : q ≤ n) (u : (Fin (1 + n) → ℝ) → ℝ)
    (hu : LocallyIntegrableOn u {x | 0 < x 0} volume)
    (hweak : ∀ φ : (Fin (1 + n) → ℝ) → ℝ,
      ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ → tsupport φ ⊆ {x | 0 < x 0} →
      (∫ x in {x | 0 < x 0}, u x *
        (fderiv ℝ φ x (leftCoordinateInclusion 1 n (fun _ => 1)) +
          ∑ i : Fin q, fderiv ℝ
            (fun y => fderiv ℝ φ y (liftRightField 1 (G.horizontalFields hq i) y)) x
            (liftRightField 1 (G.horizontalFields hq i) x))) = 0) :
    HasWeakHormanderEquation {x | 0 < x 0} (horizontalHeatFields G hq) 0 0 u := by
  refine ⟨hu, contDiffOn_const, ?_⟩
  intro φ hφ hcompact hsupp
  simpa only [hormanderAdjointTest_horizontalHeatFields G hq φ hφ, Pi.zero_apply,
    MulZeroClass.zero_mul, integral_zero] using hweak φ hφ hcompact hsupp

/-- Spatial bracket spanning and the weak heat identity give a unique smooth representative. -/
theorem exists_unique_smooth_heat_representative_of_integral_identity {n q : ℕ}
    (G : HomogeneousGroup n) (hq : q ≤ n)
    (hspan : bracketSpansOn Set.univ (G.horizontalFields hq))
    (u : (Fin (1 + n) → ℝ) → ℝ)
    (hu : LocallyIntegrableOn u {x | 0 < x 0} volume)
    (hweak : ∀ φ : (Fin (1 + n) → ℝ) → ℝ,
      ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ → tsupport φ ⊆ {x | 0 < x 0} →
      (∫ x in {x | 0 < x 0}, u x *
        (fderiv ℝ φ x (leftCoordinateInclusion 1 n (fun _ => 1)) +
          ∑ i : Fin q, fderiv ℝ
            (fun y => fderiv ℝ φ y (liftRightField 1 (G.horizontalFields hq i) y)) x
            (liftRightField 1 (G.horizontalFields hq i) x))) = 0) :
    ∃ v : (Fin (1 + n) → ℝ) → ℝ,
      ContDiffOn ℝ (⊤ : ℕ∞) v {x | 0 < x 0} ∧
      u =ᵐ[volume.restrict {x | 0 < x 0}] v ∧
      ∀ w : (Fin (1 + n) → ℝ) → ℝ,
        ContDiffOn ℝ (⊤ : ℕ∞) w {x | 0 < x 0} →
        u =ᵐ[volume.restrict {x | 0 < x 0}] w → Set.EqOn v w {x | 0 < x 0} := by
  have hbracket : LieAlgebraSpansOn {x | 0 < x 0} (horizontalHeatFields G hq) := by
    intro x _
    exact lieAlgebraSpansOn_horizontalHeatFields G hq hspan x (Set.mem_univ x)
  obtain ⟨v, hv, huv⟩ := Hormander.Interface.exists_smooth_aeRepresentative
    (isOpen_positive_time n) (horizontalHeatFields G hq) 0 0 u
    (fun i => (contDiff_horizontalHeatFields G hq i).contDiffOn) hbracket contDiffOn_const
    (hasWeakHormanderEquation_horizontalHeatFields_of_integral_identity G hq u hu hweak)
  refine ⟨v, hv, huv, ?_⟩
  intro w hw huw
  exact Measure.eqOn_open_of_ae_eq (huv.symm.trans huw) (isOpen_positive_time n)
    hv.continuousOn hw.continuousOn

end HeatKernel
