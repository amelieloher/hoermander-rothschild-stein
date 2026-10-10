-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Poincare.WhitneyEnergyCost
public import HeatKernel.Poincare.CarnotWhitneyEdgeCost

/-! Simultaneous normalized gradient costs and neighboring average estimates. -/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set Metric MeasureTheory RothschildStein
open scoped NNReal ENNReal

namespace HeatKernel

/-- A single family of finite normalized energies supplies every local oscillation
bound and every neighboring-average edge bound in the selected family. -/
theorem exists_boundaryBall_energy_family {N q : ℕ}
    (G : HomogeneousGroup N) (hq : q ≤ N) (hqpos : 0 < q)
    (hspan : bracketSpansOn univ (G.horizontalFields hq))
    (hw : ∀ i : Fin q, G.weight (Fin.castLE hq i) = 1)
    {x : CarnotPoint G hq hqpos hspan} {r κ p : ℝ} (hr : 0 < r) (hκ : 80 < κ)
    (C : Set (CarnotPoint G hq hqpos hspan)) (hCU : C ⊆ ball x r)
    (hp : 1 ≤ p) (u : (Fin N → ℝ) → ℝ)
    (hu : ContDiffOn ℝ 1 u (horizontalBall (G.horizontalFields hq) x r)) :
    let a := fun z : C => infDist z.val (ball x r)ᶜ / κ
    let A := fun z : C => horizontalBall (G.horizontalFields hq) z.val (a z)
    let V := fun z : C => horizontalBall (G.horizontalFields hq) z.val (20 * a z)
    let I := fun z : C => ∫⁻ y in horizontalBall (G.horizontalFields hq) z.val (80 * a z),
      ENNReal.ofReal (horizontalGradientNorm (G.horizontalFields hq) u y ^ p)
    let c := fun z : C => ⨍ y in V z, u y
    ∃ h : C → ℝ≥0,
      (∀ z, (h z : ℝ≥0∞) = (I z / volume (A z)) ^ (1 / p) ∧
        volume (A z) * ((h z ^ p : ℝ≥0) : ℝ≥0∞) = I z ∧
        eLpNorm (fun y => u y - c z) (ENNReal.ofReal p) (volume.restrict (V z)) ≤
          ENNReal.ofReal (((2 : ℝ) ^ G.homogeneousDimension) ^ (1 / p) * (3 * (20 * a z))) *
            volume (A z) ^ (1 / p) * h z) ∧
      (∀ z w, (ball z.val (5 * a z) ∩ ball w.val (5 * a w)).Nonempty →
        |c z - c w| ≤ (60 * (((2 : ℝ) ^ G.homogeneousDimension) ^ (1 / p)) ^ 2) *
          (a z * (h z : ℝ) + a w * (h w : ℝ))) := by
  dsimp only
  have hex := fun z : C => exists_boundaryBall_energy_cost G hq hqpos hspan hw hr hκ
    (hCU z.property) hp u hu
  dsimp only at hex
  choose h hh using hex
  refine ⟨h, hh, ?_⟩
  intro z w hmeet
  exact abs_sub_le_boundaryBall_edge_cost G hq hqpos hspan hw hr hκ
    (hCU z.property) (hCU w.property) hp rfl rfl hmeet u _ _ (h z) (h w)
    (hh z).2.2 (hh w).2.2

end HeatKernel
