-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Moser.WeakSolutionOscillation
public import HeatKernel.Geometry.BallVolume
import Mathlib.Tactic

/-! # Essential oscillation decay on horizontal cylinders -/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set MeasureTheory TopologicalSpace RothschildStein Filter
namespace HeatKernel

/-- An open time interval times a positive-radius horizontal ball has nonzero
restricted space-time volume. -/
theorem volume_restrict_horizontal_cylinder_ne_zero {N q : ℕ}
    (G : HomogeneousGroup N) (hq : q ≤ N) (hqpos : 0 < q)
    (hspan : bracketSpansOn univ (G.horizontalFields hq))
    (x : Fin N → ℝ) {a b r : ℝ} (hab : a < b) (hr : 0 < r) :
    (volume : Measure (ℝ × (Fin N → ℝ))).restrict
      (Ioo a b ×ˢ horizontalBall (G.horizontalFields hq) x r) ≠ 0 := by
  rw [Ne, Measure.restrict_eq_zero]
  apply ne_of_gt
  apply (isOpen_Ioo.prod (isOpen_horizontalBall G hq hqpos hspan x r)).measure_pos volume
  refine (nonempty_Ioo.mpr hab).prod ⟨x, ?_⟩
  simpa only [horizontalBall, mem_ofPred_eq, horizontalL2Distance_self] using
    ENNReal.ofReal_pos.mpr hr

/-- A uniform Harnack constant gives the same strict oscillation contraction
on every horizontal cylinder. The Harnack estimate is the explicit analytic
input; cylinder positivity and containment require no additional hypotheses. -/
theorem IsLocalWeakSolution.essential_oscillation_on_cylinder_le_of_harnack
    {N q : ℕ} (G : HomogeneousGroup N) (hq : q ≤ N) (hqpos : 0 < q)
    (hw : ∀ i : Fin q, G.weight (Fin.castLE hq i) = 1)
    (hspan : bracketSpansOn univ (G.horizontalFields hq))
    (x : Fin N → ℝ) (t r H : ℝ) (hr : 0 < r) (hH : 1 ≤ H)
    (a : ℝ → (Fin N → ℝ) → Fin q → Fin q → ℝ)
    (harnack : ∀ w : ℝ → (Fin N → ℝ) → ℝ,
      IsLocalWeakSolution G hq hqpos hw hspan a
        ⟨Ioo (t - 4 * r ^ 2) t, isOpen_Ioo⟩
        ⟨horizontalBall (G.horizontalFields hq) x (2 * r),
          isOpen_horizontalBall G hq hqpos hspan x (2 * r)⟩ w →
      (∀ᵐ z ∂volume.restrict (Ioo (t - 4 * r ^ 2) t ×ˢ
        horizontalBall (G.horizontalFields hq) x (2 * r)), 0 ≤ w z.1 z.2) →
      essSup (fun z => ENNReal.ofReal (w z.1 z.2))
        (volume.restrict (Ioo (t - 3 * r ^ 2) (t - 2 * r ^ 2) ×ˢ
          horizontalBall (G.horizontalFields hq) x r)) ≤
      ENNReal.ofReal H * essInf (fun z => ENNReal.ofReal (w z.1 z.2))
        (volume.restrict (Ioo (t - r ^ 2) t ×ˢ horizontalBall (G.horizontalFields hq) x r)))
    {u : ℝ → (Fin N → ℝ) → ℝ}
    (hu : IsLocalWeakSolution G hq hqpos hw hspan a
      ⟨Ioo (t - 4 * r ^ 2) t, isOpen_Ioo⟩
      ⟨horizontalBall (G.horizontalFields hq) x (2 * r),
        isOpen_horizontalBall G hq hqpos hspan x (2 * r)⟩ u)
    (hupper : IsBoundedUnder (· ≤ ·)
      (ae (volume.restrict (Ioo (t - 4 * r ^ 2) t ×ˢ
        horizontalBall (G.horizontalFields hq) x (2 * r)))) (Function.uncurry u))
    (hlower : IsBoundedUnder (· ≥ ·)
      (ae (volume.restrict (Ioo (t - 4 * r ^ 2) t ×ˢ
        horizontalBall (G.horizontalFields hq) x (2 * r)))) (Function.uncurry u)) :
    1 - 1 / (2 * H) ∈ Ioo (0 : ℝ) 1 ∧
    essSup (Function.uncurry u)
        (volume.restrict (Ioo (t - r ^ 2) t ×ˢ horizontalBall (G.horizontalFields hq) x r)) -
      essInf (Function.uncurry u)
        (volume.restrict (Ioo (t - r ^ 2) t ×ˢ horizontalBall (G.horizontalFields hq) x r)) ≤
      (1 - 1 / (2 * H)) *
        (essSup (Function.uncurry u)
            (volume.restrict (Ioo (t - 4 * r ^ 2) t ×ˢ horizontalBall (G.horizontalFields hq) x (2 * r))) -
          essInf (Function.uncurry u)
            (volume.restrict (Ioo (t - 4 * r ^ 2) t ×ˢ horizontalBall (G.horizontalFields hq) x (2 * r)))) := by
  refine ⟨harnack_oscillation_factor_mem_Ioo hH, ?_⟩
  have hb : horizontalBall (G.horizontalFields hq) x r ⊆
      horizontalBall (G.horizontalFields hq) x (2 * r) := by
    intro y hy
    exact lt_of_lt_of_le hy (ENNReal.ofReal_le_ofReal (by linarith))
  apply IsLocalWeakSolution.essential_oscillation_le_of_harnack_estimate
    G hq hqpos hw hspan
    (volume_restrict_horizontal_cylinder_ne_zero G hq hqpos hspan x (by nlinarith [sq_pos_of_pos hr]) hr)
    (volume_restrict_horizontal_cylinder_ne_zero G hq hqpos hspan x (by nlinarith [sq_pos_of_pos hr]) hr)
    (Measure.restrict_mono ?_ le_rfl) (Measure.restrict_mono ?_ le_rfl)
    hH harnack hu hupper hlower
  · intro z hz
    exact ⟨⟨by nlinarith [hz.1.1, sq_pos_of_pos hr],
      by nlinarith [hz.1.2, sq_pos_of_pos hr]⟩, hb hz.2⟩
  · intro z hz
    exact ⟨⟨by nlinarith [hz.1.1, sq_pos_of_pos hr], hz.1.2⟩, hb hz.2⟩

end HeatKernel
