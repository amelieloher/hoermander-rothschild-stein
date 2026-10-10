-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Kernel.SmoothLocalWeakSolutions
public import HeatKernel.Kernel.SliceWeakHeatEquation

/-! # Classical heat equations on product spacetime

A smooth product-spacetime function satisfying the heat equation on every
positive-time spatial slice is a local weak solution on every contained cylinder.
-/

@[expose] public section

noncomputable section

open TopologicalSpace
open RothschildStein

namespace HeatKernel

/-- Smooth classical heat equations on spatial slices give the full local weak-solution predicate. -/
theorem isLocalWeakSolution_of_smooth_classical_heat_equation {n q : ℕ}
    (G : HomogeneousGroup n) (hq : q ≤ n) (hqpos : 0 < q)
    (hw : ∀ i : Fin q, G.weight (Fin.castLE hq i) = 1)
    (hspan : bracketSpansOn Set.univ (G.horizontalFields hq))
    (I : Opens ℝ) (U : Opens (Fin n → ℝ)) (hI : ∀ t ∈ I, 0 < t)
    (u : ℝ → (Fin n → ℝ) → ℝ)
    (hu : ContDiffOn ℝ (⊤ : ℕ∞) (fun p : ℝ × (Fin n → ℝ) => u p.1 p.2)
      {p | 0 < p.1})
    (hheat : ∀ t, 0 < t → ∀ x, deriv (fun s => u s x) t =
      sumSquares (G.horizontalFields hq) (u t) x) :
    IsLocalWeakSolution G hq hqpos hw hspan
      (fun _ _ i j => if i = j then 1 else 0) I U u := by
  let v : (Fin (1 + n) → ℝ) → ℝ :=
    fun z => u (timeSpaceCoordinates n z).1 (timeSpaceCoordinates n z).2
  have hv : ContDiffOn ℝ (⊤ : ℕ∞) v {z | 0 < z 0} :=
    hu.comp (timeSpaceCoordinates n).contDiff.contDiffOn (fun z hz => hz)
  have heq {z : Fin (1 + n) → ℝ} (hz : 0 < z 0) :=
    coordinate_heat_equation_of_slice_equation (G.horizontalFields hq)
    (G.horizontalFields_contDiff hq) v hv
    (show ∀ t, 0 < t → ∀ x,
      deriv (fun s => v ((timeSpaceCoordinates n).symm (s, x))) t =
        sumSquares (G.horizontalFields hq)
          (fun y => v ((timeSpaceCoordinates n).symm (t, y))) x from by
      intro t ht x
      simpa only [v, ContinuousLinearEquiv.apply_symm_apply] using hheat t ht x) hz
  simpa only [v, ContinuousLinearEquiv.apply_symm_apply] using
    isLocalWeakSolution_of_coordinate_heat_equation G hq hqpos hw hspan I U hI v hv
      (fun z hz => heq hz)

end HeatKernel
