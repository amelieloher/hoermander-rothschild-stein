-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Kernel.AlmostEverywhereHeatRepresentatives
public import HeatKernel.Kernel.GlobalHorizontalHeatGraph
public import HeatKernel.Kernel.AlmostEverywhereHorizontalOrbitTests

/-! # Smooth representatives of concrete horizontal heat orbits

The concrete resolvent graph supplies the weak equation from scalar
representatives whose time sections agree almost everywhere with the orbit.
-/

@[expose] public section
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace HeatKernel
open RothschildStein

/-- Locally integrable scalar representatives with almost-everywhere time sections determine the smooth concrete heat orbit at every positive time. -/
theorem exists_smooth_global_horizontal_heat_representative_of_ae_sections {n q : ℕ}
    (G : HomogeneousGroup n) (hq : q ≤ n)
    (hspan : bracketSpansOn Set.univ (G.horizontalFields hq))
    (f : Lp ℝ 2 (volume : Measure (Fin n → ℝ)))
    (u : (Fin (1 + n) → ℝ) → ℝ)
    (hu : LocallyIntegrableOn u {x | 0 < x 0} volume)
    (hslice : ∀ᵐ t ∂volume, 0 < t →
      (fun x => u ((timeSpaceCoordinates n).symm (t, x))) =ᵐ[volume] globalHorizontalHeatOperator G hq t.toNNReal f)
    :
    let T := fun t : ℝ => globalHorizontalHeatOperator G hq t.toNNReal f
    ∃ v : (Fin (1 + n) → ℝ) → ℝ,
      ContDiffOn ℝ (⊤ : ℕ∞) v {x | 0 < x 0} ∧
      u =ᵐ[volume.restrict {x | 0 < x 0}] v ∧
      (∀ t : ℝ, 0 < t →
        ∃ h : MemLp (fun x => v ((timeSpaceCoordinates n).symm (t, x))) 2 volume,
          h.toLp (fun x => v ((timeSpaceCoordinates n).symm (t, x))) = T t) ∧
      (∀ x : Fin (1 + n) → ℝ, 0 < x 0 →
        fderiv ℝ v x (leftCoordinateInclusion 1 n (fun _ => 1)) =
          ∑ i : Fin q, fderiv ℝ
            (fun y => fderiv ℝ v y (liftRightField 1 (G.horizontalFields hq i) y)) x
            (liftRightField 1 (G.horizontalFields hq i) x)) ∧
      (∀ w : (Fin (1 + n) → ℝ) → ℝ,
        ContDiffOn ℝ (⊤ : ℕ∞) w {x | 0 < x 0} →
        u =ᵐ[volume.restrict {x | 0 < x 0}] w → Set.EqOn v w {x | 0 < x 0}) := by
  let T := fun t : ℝ => globalHorizontalHeatOperator G hq t.toNNReal f
  apply exists_smooth_L2_heat_representative_of_ae_sections G hq hspan T
    (contDiffOn_globalHorizontalHeatOperator G hq f).continuousOn u hu hslice
  intro φ hφ hc hs
  exact (setIntegral_positive_heat_test_eq_zero_of_ae_horizontal_resolvent_orbit
    G hq T u φ hu hslice hφ hc hs
    (contDiffOn_globalHorizontalHeatOperator G hq f)
    (fun t ht => inverseResolventGraph_globalHorizontalHeatOperator G hq f ht)).2

end HeatKernel
