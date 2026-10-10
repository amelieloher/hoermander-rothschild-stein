-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Sobolev.LocalEnergyLinearPoincare
import Mathlib.Tactic
import all HeatKernel.Geometry.CarnotPoint

/-! # Interior linear-tent Poincaré for local horizontal energy functions -/

@[expose] public section
open Set MeasureTheory Metric RothschildStein TopologicalSpace
open scoped ENNReal
namespace HeatKernel.CarnotPoint

/-- Same-ball Poincaré gives the linear-tent inequality for a local energy
function whenever the closed horizontal ball lies inside its domain. -/
theorem lintegral_tent_sub_weightedMean_le_of_interior_energy_poincare {N q : ℕ}
    (G : HomogeneousGroup N) (hq : q ≤ N) (hqpos : 0 < q)
    (hspan : bracketSpansOn univ (G.horizontalFields hq))
    (hw : ∀ i : Fin q, G.weight (Fin.castLE hq i) = 1)
    (x : CarnotPoint G hq hqpos hspan) {r : ℝ} (hr : 0 < r)
    (U : Opens (Fin N → ℝ))
    (hroom : {y : Fin N → ℝ | horizontalL2Distance (G.horizontalFields hq) x y ≤
      ENNReal.ofReal r} ⊆ (U : Set (Fin N → ℝ)))
    (f : (Fin N → ℝ) → ℝ) (g : Fin q → (Fin N → ℝ) → ℝ)
    (hf : MemLocalEnergy U (G.horizontalFields hq) f)
    (hg : ∀ i, hasWeakWordDeriv (G.horizontalFields hq) U [i] f (g i)) {P : ℝ≥0∞}
    (hpoincare : ∀ s : ℝ, 0 < s → s ≤ r →
      (∫⁻ y in ball x s, ENNReal.ofReal ((f y -
        (∫ z in ball x s, f z ∂volume G hq hqpos hspan) /
          (volume G hq hqpos hspan).real (ball x s)) ^ 2) ∂volume G hq hqpos hspan) ≤
        P * ENNReal.ofReal s ^ 2 * ∫⁻ y in ball x s, ENNReal.ofReal (∑ i, (g i y) ^ 2) ∂volume G hq hqpos hspan) :
    (∫⁻ y, ENNReal.ofReal (max (1 - dist x y / r) 0) *
      ENNReal.ofReal ((f y - Sobolev.weightedMean (volume G hq hqpos hspan)
        (fun z => max (1 - dist x z / r) 0) (fun y => f y)) ^ 2) ∂volume G hq hqpos hspan) ≤
      ((P * ENNReal.ofReal (r / 2) ^ 2) +
        ENNReal.ofReal (1 + (2 : ℝ) ^ G.homogeneousDimension) * P * ENNReal.ofReal r ^ 2) *
        ∫⁻ y, ENNReal.ofReal (max (1 - dist x y / r) 0) * ENNReal.ofReal (∑ i, (g i y) ^ 2) ∂volume G hq hqpos hspan := by
  obtain ⟨V, hKV, hVc, hVU⟩ := exists_precompact_open_of_isCompact U
    (isCompact_horizontal_closedBall G hq hqpos hspan hw x hr.le) hroom
  apply lintegral_tent_sub_weightedMean_le_of_local_energy_poincare G hq hqpos hspan hw x hr
    U V hVc hVU _ f g hf hg hpoincare
  intro y hy
  apply hKV
  change horizontalL2Distance (G.horizontalFields hq) x y ≤ ENNReal.ofReal r
  exact le_of_lt (show horizontalL2Distance (G.horizontalFields hq) x y < ENNReal.ofReal r from hy)

end HeatKernel.CarnotPoint
