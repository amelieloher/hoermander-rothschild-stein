-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Sobolev.HorizontalSobolevVolume
public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
public import Mathlib.MeasureTheory.Function.LpSeminorm.Indicator
import Mathlib.Tactic

/-! # Uniform spatial Sobolev estimates with literal volume scaling -/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
open Set MeasureTheory TopologicalSpace RothschildStein
namespace HeatKernel

/-- One constant gives the spatial Sobolev estimate for ordinary volume at every radius. -/
theorem exists_uniform_unnormalized_horizontal_sobolev_constant {N q : ℕ}
    (G : HomogeneousGroup N) (hq : q ≤ N) (hqpos : 0 < q)
    (hspan : bracketSpansOn univ (G.horizontalFields hq))
    (hw : ∀ i : Fin q, G.weight (Fin.castLE hq i) = 1)
    {ν : ℝ} (hν : max 2 (G.homogeneousDimension : ℝ) < ν) :
    ∃ C : ℝ, 0 < C ∧ ∀ (U : Opens (Fin N → ℝ)),
      volume (U : Set (Fin N → ℝ)) ≠ ⊤ → ∀ r : ℝ, 0 < r →
      ∀ v : zeroBoundaryGraph U (G.horizontalFields hq),
      eLpNorm (v : GradientSpace (N := N) ⊤ q).fst
        (ENNReal.ofReal (2 * ν / (ν - 2))) volume ^ 2 ≤
        ENNReal.ofReal ((C *
          (volume.real (horizontalBall (G.horizontalFields hq) 0 r)) ^ (-2 / ν)) *
          (r ^ 2 * ‖(v : GradientSpace (N := N) ⊤ q).snd‖ ^ 2 +
            ‖(v : GradientSpace (N := N) ⊤ q).fst‖ ^ 2)) := by
  let ν' := (ν + max 2 (G.homogeneousDimension : ℝ)) / 2
  have hν₂ : 2 < ν := lt_of_le_of_lt (le_max_left _ _) hν
  have hν'₂ : 2 < ν' := by dsimp [ν']; linarith [le_max_left 2 (G.homogeneousDimension : ℝ)]
  have hQ : (G.homogeneousDimension : ℝ) ≤ ν' := by
    dsimp [ν']
    linarith [le_max_right 2 (G.homogeneousDimension : ℝ)]
  have hν'ν : ν' < ν := by dsimp [ν']; linarith
  have hp := Sobolev.two_lt_sobolevExponent hν₂
  have hpp := Sobolev.sobolevExponent_lt_of_lt hν'₂ hν'ν
  refine ⟨Sobolev.horizontalSobolevConstant G.homogeneousDimension ν' (2 * ν / (ν - 2)),
    Sobolev.horizontalSobolevConstant_pos _ hν'₂ hp hpp, ?_⟩
  intro U hfinite r hr v
  have hexp : 2 / (2 * ν / (ν - 2)) - 1 = -2 / ν := by
    rw [neg_div]
    linarith [Sobolev.sobolev_volume_exponent hν₂]
  simpa only [hexp] using
    Sobolev.eLpNorm_sq_le_horizontal_volume_power G hq hqpos hspan hw U hfinite hr
      hν'₂ hQ hp hpp v

end HeatKernel
