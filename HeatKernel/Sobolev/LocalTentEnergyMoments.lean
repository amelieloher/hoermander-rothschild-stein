-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Sobolev.LocalWeightedMoments
public import HeatKernel.Sobolev.DistanceTentPowers
public import HeatKernel.Geometry.BallVolume
public import RothschildStein.Definitions.HomogeneousGroup.horizontalFields_contDiff
import Mathlib.Tactic
import all HeatKernel.Geometry.CarnotPoint
import all Mathlib.Basic.Real.Basic

/-! # Finite distance-tent moments of local horizontal energy functions -/

@[expose] public section
open Set MeasureTheory Metric TopologicalSpace RothschildStein
namespace HeatKernel.CarnotPoint

/-- Every positive natural distance-tent power has integrable value variance and
weak-gradient energy moments on a compact interior horizontal ball. -/
theorem integrable_local_tent_energy_moments {N q : ℕ}
    (G : HomogeneousGroup N) (hq : q ≤ N) (hqpos : 0 < q)
    (hspan : bracketSpansOn univ (G.horizontalFields hq))
    (hw : ∀ i : Fin q, G.weight (Fin.castLE hq i) = 1)
    (x : CarnotPoint G hq hqpos hspan) {r : ℝ} (hr : 0 < r)
    (U : Opens (Fin N → ℝ))
    (hroom : {y : Fin N → ℝ | horizontalL2Distance (G.horizontalFields hq) x y ≤
      ENNReal.ofReal r} ⊆ (U : Set (Fin N → ℝ)))
    (f : (Fin N → ℝ) → ℝ) (g : Fin q → (Fin N → ℝ) → ℝ)
    (hf : MemLocalEnergy U (G.horizontalFields hq) f)
    (hg : ∀ i, hasWeakWordDeriv (G.horizontalFields hq) U [i] f (g i))
    {n : ℕ} (hn : 0 < n) :
    (∀ c : ℝ, Integrable (fun y : CarnotPoint G hq hqpos hspan =>
      max (1 - dist x y / r) 0 ^ n * (f y - c) ^ 2) (volume G hq hqpos hspan)) ∧
    Integrable (fun y : CarnotPoint G hq hqpos hspan =>
      max (1 - dist x y / r) 0 ^ n * ∑ i, (g i y) ^ 2) (volume G hq hqpos hspan) := by
  obtain ⟨hm, _, hb, hs⟩ := Sobolev.distance_tent_pow_properties x hr hn
  have hball : ball x r = horizontalBall (G.horizontalFields hq) x r := by
    ext y
    rw [mem_ball, ← edist_lt_ofReal, edist_comm, edist_eq]
    rfl
  have hsupport : Function.support (fun y : CarnotPoint G hq hqpos hspan =>
      max (1 - dist x y / r) 0 ^ n) ⊆
      {y : Fin N → ℝ | horizontalL2Distance (G.horizontalFields hq) x y ≤ ENNReal.ofReal r} := by
    intro y hy
    have hmem := hs hy
    rw [hball] at hmem
    exact le_of_lt (show horizontalL2Distance (G.horizontalFields hq) x y < ENNReal.ofReal r from hmem)
  have H := Sobolev.integrable_weighted_local_energy_moments U (G.horizontalFields hq)
    (G.horizontalFields_contDiff hq) hf hg
    (isCompact_horizontal_closedBall G hq hqpos hspan hw x hr.le) hroom hm hb hsupport
  convert H using 1 <;> rfl

end HeatKernel.CarnotPoint
