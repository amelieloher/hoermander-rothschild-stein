-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Kernel.GlobalHorizontalResolvent
public import HeatKernel.Kernel.CoordinateHeatOrbitPairings
public import HeatKernel.Kernel.CoordinateHeatEquation

/-! # Compact coordinate tests in the global horizontal resolvent graph

Every spatial slice of a smooth compact spacetime test is in the
horizontal operator domain, with the literal lifted sum of squares as its generator.
-/

@[expose] public section

noncomputable section

open MeasureTheory RothschildStein

namespace HeatKernel

/-- Compact coordinate test slices have the required negative lifted sum of squares in the resolvent graph. -/
theorem inverseResolventGraph_globalHorizontalForm_coordinate_test_slice {n q : ℕ}
    (G : HomogeneousGroup n) (hq : q ≤ n)
    (φ : (Fin (1 + n) → ℝ) → ℝ) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hc : HasCompactSupport φ) (t : ℝ) (ht : 0 < t) :
    InverseResolventGraph (globalHorizontalFormResolvent G hq)
      ((memLp_two_coordinate_test_slice φ hφ hc t).toLp
        (fun x => φ ((timeSpaceCoordinates n).symm (t, x))))
      (-((memLp_two_lifted_sumSquares_test_slice (G.horizontalFields hq)
        (G.horizontalFields_contDiff hq) φ hφ hc t).toLp
        (fun x => sumSquares (fun i => liftRightField 1 (G.horizontalFields hq i)) φ
          ((timeSpaceCoordinates n).symm (t, x))))) := by
  obtain ⟨hC, hcompact⟩ := smooth_compact_inverse_timeSpace_test φ hφ hc
  have hf : ContDiff ℝ (⊤ : ℕ∞) (fun x => φ ((timeSpaceCoordinates n).symm (t, x))) :=
    hC.comp (contDiff_const.prodMk contDiff_id)
  have hcf : HasCompactSupport (fun x => φ ((timeSpaceCoordinates n).symm (t, x))) :=
    hasCompactSupport_spatial_slice _ hcompact t
  apply inverseResolventGraph_globalHorizontalForm_of_smooth_compact G hq _ hf hcf _ _
    (memLp_two_coordinate_test_slice φ hφ hc t).coeFn_toLp
  have hp := memLp_two_lifted_sumSquares_test_slice (G.horizontalFields hq)
    (G.horizontalFields_contDiff hq) φ hφ hc t
  filter_upwards [Lp.coeFn_neg (hp.toLp _), hp.coeFn_toLp] with x hneg hx
  change (-hp.toLp _) x = -sumSquares (G.horizontalFields hq)
    (fun y => φ ((timeSpaceCoordinates n).symm (t, y))) x
  rw [hneg]
  change -(hp.toLp _ x) = _
  rw [hx]
  congr 1
  exact (sumSquares_spatial_coordinate_slice _ (G.horizontalFields_contDiff hq) φ hφ.contDiffOn ht x).symm

end HeatKernel
