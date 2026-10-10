-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Sobolev.ZeroBoundaryHorizontalNash
public import HeatKernel.Sobolev.ScaledEnergyStrongFromNash
public import HeatKernel.Sobolev.SobolevExponents
import Mathlib.Tactic
import all Mathlib.Basic.Real.Basic

/-! # Strong horizontal Sobolev estimates on zero-boundary domains -/

@[expose] public section
open Set MeasureTheory TopologicalSpace RothschildStein
open scoped ENNReal
namespace HeatKernel.Sobolev

/-- Horizontal averaging and form truncations give a strong subcritical Sobolev estimate. -/
theorem eLpNorm_sq_le_horizontal_scaled_energy {N q : ℕ}
    (G : HomogeneousGroup N) (hq : q ≤ N) (hqpos : 0 < q)
    (hspan : bracketSpansOn univ (G.horizontalFields hq))
    (hw : ∀ i : Fin q, G.weight (Fin.castLE hq i) = 1)
    (U : Opens (Fin N → ℝ)) (hfinite : volume (U : Set (Fin N → ℝ)) ≠ ⊤)
    {r ν p : ℝ} (hr : 0 < r) (hν : 2 < ν) (hQ : (G.homogeneousDimension : ℝ) ≤ ν)
    (hp : 2 < p) (hpp : p < 2 * ν / (ν - 2))
    (v : zeroBoundaryGraph U (G.horizontalFields hq)) :
    eLpNorm (v : GradientSpace (N := N) ⊤ q).fst (ENNReal.ofReal p) volume ^ 2 ≤
      ENNReal.ofReal (subcriticalSobolevConstant
        (((Real.sqrt (576 * (66 : ℝ) ^ G.homogeneousDimension) + 2) ^ 2 *
          2 ^ (ν / (ν + 2))) *
          (Real.sqrt ((volume.real (horizontalBall (G.horizontalFields hq) 0 r))⁻¹)) ^
            (4 / (ν + 2))) (4 / (ν + 2)) p *
        (r ^ 2 * ‖(v : GradientSpace (N := N) ⊤ q).snd‖ ^ 2 +
          ‖(v : GradientSpace (N := N) ⊤ q).fst‖ ^ 2)) := by
  have hb := nash_exponent_mem_Ioo hν
  apply eLpNorm_sq_le_scaled_energy_of_nash U (G.horizontalFields hq)
    (fun i => G.horizontalFields_contDiff hq i) hfinite r
    (b := 4 / (ν + 2)) (by positivity) hb.1.le hb.2 hp
    (by rw [weakSobolevExponent_nash hν]; exact hpp) _ v
  intro z
  rw [nash_energy_exponent hν]
  exact norm_sq_le_horizontal_nash_on_zeroBoundaryGraph G hq hqpos hspan hw U hfinite hr
    (by linarith) hQ z

end HeatKernel.Sobolev
