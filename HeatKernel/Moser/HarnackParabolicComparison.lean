-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Moser.HarnackUniformEstimates
public import HeatKernel.Moser.HarnackUniformComparison
import Mathlib.Tactic

/-! # Parabolic Harnack for uniformly elliptic matrix equations

The local logarithmic and power estimates give a uniform Harnack comparison
for every nonnegative local weak representative. The constant is normalized
as `max 1 C`, and the later target cylinder shares the outer top time.
-/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set MeasureTheory TopologicalSpace RothschildStein
open scoped ENNReal
namespace HeatKernel

/-- A uniform Harnack constant compares the earlier essential supremum with
the later essential infimum for nonnegative matrix weak solutions. -/
theorem exists_uniform_matrix_parabolic_harnack
    {N q : ℕ} (G : HomogeneousGroup N) (hq : q ≤ N) (hqpos : 0 < q)
    (hspan : bracketSpansOn univ (G.horizontalFields hq))
    (hw : ∀ i : Fin q, G.weight (Fin.castLE hq i) = 1)
    (ell upper : ℝ) (hell : 0 < ell) (hupper : 0 ≤ upper) :
    ∃ H : ℝ, 1 ≤ H ∧
      ∀ (x : CarnotPoint G hq hqpos hspan) (t r : ℝ), 0 < r →
      ∀ (coeff : ℝ → (Fin N → ℝ) → Fin q → Fin q → ℝ)
      (u : ℝ × CarnotPoint G hq hqpos hspan → ℝ),
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
      let μ := volume.prod (CarnotPoint.volume G hq hqpos hspan)
      essSup (fun y => ENNReal.ofReal (u y)) (μ.restrict (harnackEarlierTargetCylinder x t r)) ≤
        ENNReal.ofReal H *
          essInf (fun y => ENNReal.ofReal (u y)) (μ.restrict (harnackLaterTargetCylinder x t r)) := by
  obtain ⟨p₀, Aminus, Aplus, Cminus, Cplus, κminus, κplus,
      hp₀, hp₀two, hAminus, hAplus, hCminus, hCplus, hκminus, hκplus, hestimates⟩ :=
    exists_uniform_matrix_hasHarnackCylinderEstimates G hq hqpos hspan hw ell upper hell hupper
  exact exists_uniform_matrix_parabolic_harnack_of_local_estimate_supplier
    G hq hqpos hspan hw ell upper hell hupper hp₀ hp₀two hAminus hAplus
    hCminus hCplus hκminus hκplus hestimates

end HeatKernel
