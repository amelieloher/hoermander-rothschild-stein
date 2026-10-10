-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Sobolev.RealLocalTentPoincare
import Mathlib.Tactic
import all HeatKernel.Geometry.CarnotPoint

/-! # Real-integral tent Poincaré on concentric horizontal balls -/

@[expose] public section
open Set MeasureTheory Metric RothschildStein TopologicalSpace
open scoped ENNReal
namespace HeatKernel.CarnotPoint

/-- The two tent weights satisfy the real-integral estimate with the literal
normalized mean on a strictly interior concentric horizontal ball. -/
theorem integral_tent_pow_sub_mean_le_of_concentric_poincare {N q : ℕ}
    (G : HomogeneousGroup N) (hq : q ≤ N) (hqpos : 0 < q)
    (hspan : bracketSpansOn univ (G.horizontalFields hq))
    (hw : ∀ i : Fin q, G.weight (Fin.castLE hq i) = 1)
    (x : CarnotPoint G hq hqpos hspan) {r R : ℝ} (hr : 0 < r) (hrR : r < R)
    (f : (Fin N → ℝ) → ℝ) (g : Fin q → (Fin N → ℝ) → ℝ)
    (hf : MemLocalEnergy
      ⟨horizontalBall (G.horizontalFields hq) x R, isOpen_horizontalBall G hq hqpos hspan x R⟩
      (G.horizontalFields hq) f)
    (hg : ∀ i, hasWeakWordDeriv (G.horizontalFields hq)
      ⟨horizontalBall (G.horizontalFields hq) x R, isOpen_horizontalBall G hq hqpos hspan x R⟩
      [i] f (g i))
    {P : ℝ} (hP : 0 < P) (α : ℕ) (hα : α = 1 ∨ α = 2)
    (hpoincare : ∀ s : ℝ, 0 < s → s ≤ r →
      (∫⁻ y in ball x s, ENNReal.ofReal ((f y -
        (∫ z in ball x s, f z ∂volume G hq hqpos hspan) /
          (volume G hq hqpos hspan).real (ball x s)) ^ 2) ∂volume G hq hqpos hspan) ≤
        ENNReal.ofReal P * ENNReal.ofReal s ^ 2 * ∫⁻ y in ball x s, ENNReal.ofReal (∑ i, (g i y) ^ 2) ∂volume G hq hqpos hspan) :
    let w : CarnotPoint G hq hqpos hspan → ℝ := fun y => max (1 - dist x y / r) 0 ^ α
    let m := (∫ y in ball x r, w y * f y ∂volume G hq hqpos hspan) /
      (∫ y, w y ∂volume G hq hqpos hspan)
    (∫ y in ball x r, w y * (f y - m) ^ 2 ∂volume G hq hqpos hspan) ≤
      (P * ((2 : ℝ) ^ G.homogeneousDimension + 7 / 4)) * r ^ 2 *
        ∫ y in ball x r, w y * ∑ i, (g i y) ^ 2 ∂volume G hq hqpos hspan := by
  let U : TopologicalSpace.Opens (Fin N → ℝ) :=
    ⟨horizontalBall (G.horizontalFields hq) x R, isOpen_horizontalBall G hq hqpos hspan x R⟩
  apply integral_tent_pow_sub_mean_le_of_local_poincare G hq hqpos hspan hw x hr
    U _ f g hf hg hP α hα hpoincare
  intro y hy
  change horizontalL2Distance (G.horizontalFields hq) x y ≤ ENNReal.ofReal r at hy
  change horizontalL2Distance (G.horizontalFields hq) x y < ENNReal.ofReal R
  exact hy.trans_lt ((ENNReal.ofReal_lt_ofReal_iff (hr.trans hrR)).mpr hrR)

end HeatKernel.CarnotPoint
