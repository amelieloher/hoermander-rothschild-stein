-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Poincare.NormalizedSmoothPoincare

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
open Set MeasureTheory TopologicalSpace RothschildStein
open scoped ENNReal BigOperators
namespace HeatKernel

/-- The uniform normalized horizontal Poincaré inequality on a Carnot group, with
Euclidean horizontal gradient length and no auxiliary geometric parameters. -/
theorem exists_uniform_horizontal_poincare_constant
    {N q : ℕ} (G : HomogeneousGroup N) (hq : q ≤ N) (hqpos : 0 < q)
    (hw : ∀ i : Fin q, G.weight (Fin.castLE hq i) = 1)
    (hspan : bracketSpansOn univ (G.horizontalFields hq))
    (p : ℝ) (hp : 1 ≤ p) :
    let X := G.horizontalFields hq
    let B : (Fin N → ℝ) → ℝ → Set (Fin N → ℝ) :=
      fun x r => {y | horizontalL2Distance X x y < ENNReal.ofReal r}
    ∃ C : ℝ, 0 < C ∧
      ∀ (x : Fin N → ℝ) (r : ℝ), 0 < r →
      ∀ (u : (Fin N → ℝ) → ℝ) (U : Set (Fin N → ℝ)),
        IsOpen U → closure (B x r) ⊆ U → ContDiffOn ℝ 1 u U →
        (⨍ y in B x r, |u y - ⨍ z in B x r, u z| ^ p) ^ (1 / p) ≤
          C * r * (⨍ y in B x r, Real.sqrt (∑ i, fieldDerivative (X i) u y ^ 2) ^ p) ^ (1 / p) := by
  simpa only [horizontalBall, horizontalGradientNorm, fieldDerivative] using
    exists_uniform_horizontalPoincare_average_constant G hq hqpos hspan hw
      (κ := 1000) (by norm_num) 2030 (by norm_num) (by norm_num) hp

end HeatKernel
