-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Moser.HarnackReverseHolderAssembly
public import HeatKernel.Moser.HarnackEarlierReverseHolder
import Mathlib.Tactic

/-! # Uniform local Harnack estimates for matrix weak solutions

The logarithmic tails, earlier reverse Hölder family and later reciprocal
mean value family give local estimates with constants uniform over cylinders,
coefficient fields, solutions and positive perturbations.
-/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set MeasureTheory TopologicalSpace RothschildStein
open scoped ENNReal
namespace HeatKernel

/-- Nonnegative weak solutions of uniformly elliptic matrix equations satisfy
all the local Harnack estimates with uniform constants and a common shift. -/
theorem exists_uniform_matrix_hasHarnackCylinderEstimates
    {N q : ℕ} (G : HomogeneousGroup N) (hq : q ≤ N) (hqpos : 0 < q)
    (hspan : bracketSpansOn univ (G.horizontalFields hq))
    (hw : ∀ i : Fin q, G.weight (Fin.castLE hq i) = 1)
    (ell upper : ℝ) (hell : 0 < ell) (hupper : 0 ≤ upper) :
    ∃ p₀ Aminus Aplus Cminus Cplus κminus κplus : ℝ,
      0 < p₀ ∧ p₀ ≤ 2 ∧ 0 ≤ Aminus ∧ 0 ≤ Aplus ∧
      1 ≤ Cminus ∧ 1 ≤ Cplus ∧ 0 ≤ κminus ∧ 0 ≤ κplus ∧
      ∀ (x : CarnotPoint G hq hqpos hspan) (t r : ℝ), 0 < r →
      ∀ (coeff : ℝ → (Fin N → ℝ) → Fin q → Fin q → ℝ)
      (u : ℝ × CarnotPoint G hq hqpos hspan → ℝ), Measurable u →
      (∀ᵐ y ∂(volume.prod (CarnotPoint.volume G hq hqpos hspan)).restrict
        (Ioo (t - 4 * r ^ 2) t ×ˢ Metric.ball x (2 * r)), 0 ≤ u y) →
      IsLocalWeakSolution G hq hqpos hw hspan coeff
        ⟨Ioo (t - 4 * r ^ 2) t, isOpen_Ioo⟩
        ⟨horizontalBall (G.horizontalFields hq) x (2 * r),
          isOpen_horizontalBall G hq hqpos hspan x (2 * r)⟩
        (fun s y => u (s, y)) →
      (∀ i j, Measurable (fun z : ℝ × (Fin N → ℝ) => coeff z.1 z.2 i j)) →
      (∀ᵐ z : ℝ × (Fin N → ℝ) ∂volume,
        (∀ i j, coeff z.1 z.2 i j = coeff z.1 z.2 j i) ∧ ∀ ξ : Fin q → ℝ,
          ell * ∑ i, ξ i ^ 2 ≤ ∑ i, ∑ j, coeff z.1 z.2 i j * ξ i * ξ j ∧
          ∑ i, ∑ j, coeff z.1 z.2 i j * ξ i * ξ j ≤ upper * ∑ i, ξ i ^ 2) →
      HasHarnackCylinderEstimates (volume.prod (CarnotPoint.volume G hq hqpos hspan))
        x t r p₀ Aminus Aplus Cminus Cplus κminus κplus u := by
  exact exists_uniform_matrix_hasHarnackCylinderEstimates_of_reverse_holder_family
    G hq hqpos hspan hw ell upper hell hupper
    (exists_uniform_matrix_harnackEarlier_reverseHolder_family
      G hq hqpos hspan hw ell upper hell hupper)

end HeatKernel
