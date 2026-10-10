-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Sobolev.HorizontalStrongSobolev
public import HeatKernel.Sobolev.SobolevConstantScaling
import Mathlib.Tactic

/-! # Volume powers in horizontal Sobolev inequalities -/

@[expose] public section
open Set MeasureTheory TopologicalSpace RothschildStein
open scoped ENNReal
namespace HeatKernel.Sobolev

/-- A dimension-dependent coefficient for strong horizontal Sobolev estimates. -/
noncomputable def horizontalSobolevConstant (Q : ℕ) (ν p : ℝ) : ℝ :=
  subcriticalSobolevConstant
    ((Real.sqrt (576 * (66 : ℝ) ^ Q) + 2) ^ 2 * 2 ^ (ν / (ν + 2))) (4 / (ν + 2)) p

/-- The horizontal Sobolev coefficient is positive in the subcritical exponent range. -/
theorem horizontalSobolevConstant_pos (Q : ℕ) {ν p : ℝ}
    (hν : 2 < ν) (hp : 2 < p) (hpp : p < 2 * ν / (ν - 2)) :
    0 < horizontalSobolevConstant Q ν p := by
  apply subcriticalSobolevConstant_pos (by positivity) hp
  rw [weakSobolevExponent_nash hν]
  exact hpp

/-- The radius and volume dependence of the strong horizontal estimate is explicit. -/
theorem eLpNorm_sq_le_horizontal_volume_power {N q : ℕ}
    (G : HomogeneousGroup N) (hq : q ≤ N) (hqpos : 0 < q)
    (hspan : bracketSpansOn univ (G.horizontalFields hq))
    (hw : ∀ i : Fin q, G.weight (Fin.castLE hq i) = 1)
    (U : Opens (Fin N → ℝ)) (hfinite : volume (U : Set (Fin N → ℝ)) ≠ ⊤)
    {r ν p : ℝ} (hr : 0 < r) (hν : 2 < ν) (hQ : (G.homogeneousDimension : ℝ) ≤ ν)
    (hp : 2 < p) (hpp : p < 2 * ν / (ν - 2))
    (v : zeroBoundaryGraph U (G.horizontalFields hq)) :
    eLpNorm (v : GradientSpace (N := N) ⊤ q).fst (ENNReal.ofReal p) volume ^ 2 ≤
      ENNReal.ofReal ((horizontalSobolevConstant G.homogeneousDimension ν p *
        (volume.real (horizontalBall (G.horizontalFields hq) 0 r)) ^ (2 / p - 1)) *
        (r ^ 2 * ‖(v : GradientSpace (N := N) ⊤ q).snd‖ ^ 2 +
          ‖(v : GradientSpace (N := N) ⊤ q).fst‖ ^ 2)) := by
  have H := eLpNorm_sq_le_horizontal_scaled_energy G hq hqpos hspan hw U hfinite hr hν hQ hp hpp v
  have hV : 0 < volume.real (horizontalBall (G.horizontalFields hq) 0 r) :=
    ENNReal.toReal_pos (volume_horizontalBall_pos G hq hqpos hspan 0 hr).ne'
      (volume_horizontalBall_lt_top G hq hqpos hspan hw 0 hr.le).ne
  have hb := nash_exponent_mem_Ioo hν
  rw [subcriticalSobolevConstant_sqrt_inv_volume (by positivity) hV hb.1 hb.2 hp
    (by rw [weakSobolevExponent_nash hν]; exact hpp)] at H
  exact H

end HeatKernel.Sobolev
