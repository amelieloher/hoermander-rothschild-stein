-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Sobolev.SignedBallAveraging
public import HeatKernel.Poincare.CarnotBallVolume
public import HeatKernel.Sobolev.BallAveraging
import Mathlib.Tactic.Linter

/-! # Signed L¹-to-L² averaging on the horizontal metric carrier -/

@[expose] public section
open Set MeasureTheory Metric RothschildStein
open scoped ENNReal
namespace HeatKernel.CarnotPoint

/-- Literal signed horizontal ball averages satisfy the squared L¹-to-L² estimate. -/
theorem eLpNorm_signed_ballAverage_sq_le {N q : ℕ} (G : HomogeneousGroup N)
    (hq : q ≤ N) (hqpos : 0 < q)
    (hspan : bracketSpansOn univ (G.horizontalFields hq))
    (hw : ∀ i : Fin q, G.weight (Fin.castLE hq i) = 1)
    {s : ℝ} (hs : 0 < s)
    {f : CarnotPoint G hq hqpos hspan → ℝ} (hf : Measurable f) :
    eLpNorm (fun x => (∫ y in ball x s, f y ∂volume G hq hqpos hspan) /
      MeasureTheory.volume.real (horizontalBall (G.horizontalFields hq) 0 s)) 2
      (volume G hq hqpos hspan) ^ 2 ≤
      (MeasureTheory.volume (horizontalBall (G.horizontalFields hq) 0 s))⁻¹ *
        eLpNorm f 1 (volume G hq hqpos hspan) ^ 2 := by
  let _ : SecondCountableTopology (CarnotPoint G hq hqpos hspan) :=
    inferInstanceAs (SecondCountableTopology (Fin N → ℝ))
  let _ : SFinite (volume G hq hqpos hspan) :=
    inferInstanceAs (SFinite (MeasureTheory.volume : Measure (Fin N → ℝ)))
  apply Sobolev.eLpNorm_signed_ballAverage_sq_le
    (volume_horizontalBall_pos G hq hqpos hspan 0 hs).ne'
    (volume_horizontalBall_lt_top G hq hqpos hspan hw 0 hs.le).ne _ hf
  intro x
  rw [volume_ball G hq hqpos hspan hw x hs, volume_horizontalBall G hq hw 0 hs]

end HeatKernel.CarnotPoint
