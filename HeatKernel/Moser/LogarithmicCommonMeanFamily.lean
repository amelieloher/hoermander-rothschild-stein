-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Moser.LogarithmicSeparatingTime
public import HeatKernel.Moser.LogarithmicSolutionMean
public import HeatKernel.Moser.LogarithmicTentMeanCorrection
public import HeatKernel.Bridge.ParabolicCoefficientBounds
import Mathlib.Tactic
import all Mathlib.Basic.Real.Basic

/-! # Corrected logarithmic tent means supplied by local weak solutions -/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set MeasureTheory TopologicalSpace RothschildStein
namespace HeatKernel

/-- Compact-time logarithmic means of one weak solution share their value at
almost every separating time in a common interior window. The energy and
monotone correction hold on each compact interval with the same constant. -/
theorem IsLocalWeakSolution.exists_logarithmic_tent_mean_family {N q : ℕ}
    (G : HomogeneousGroup N) (hq : q ≤ N) (hqpos : 0 < q)
    (hspan : bracketSpansOn univ (G.horizontalFields hq))
    (hw : ∀ i : Fin q, G.weight (Fin.castLE hq i) = 1)
    (x : CarnotPoint G hq hqpos hspan) {r : ℝ} (hr : 0 < r)
    (coeff : ℝ → (Fin N → ℝ) → Fin q → Fin q → ℝ)
    (I : Opens ℝ) {u : ℝ → (Fin N → ℝ) → ℝ}
    (hu : IsLocalWeakSolution G hq hqpos hw hspan coeff I
      ⟨horizontalBall (G.horizontalFields hq) x (2 * r),
        isOpen_horizontalBall G hq hqpos hspan x (2 * r)⟩ u)
    (ha : ∀ i j, Measurable (fun z : ℝ × (Fin N → ℝ) => coeff z.1 z.2 i j))
    {lower upper : ℝ} (hlower : 0 ≤ lower)
    (hbound : ∀ᵐ z : ℝ × (Fin N → ℝ) ∂volume,
      (∀ i j, coeff z.1 z.2 i j = coeff z.1 z.2 j i) ∧ ∀ ξ : Fin q → ℝ,
        lower * ∑ i, ξ i ^ 2 ≤ ∑ i, ∑ j, coeff z.1 z.2 i j * ξ i * ξ j ∧
        ∑ i, ∑ j, coeff z.1 z.2 i j * ξ i * ξ j ≤ upper * ∑ i, ξ i ^ 2)
    (hu0 : ∀ᵐ z : ℝ × (Fin N → ℝ)
      ∂volume.restrict ((I : Set ℝ) ×ˢ horizontalBall (G.horizontalFields hq) x (2 * r)),
        0 ≤ u z.1 z.2)
    (A B a b : ℕ → ℝ) (hJ : ∀ n, Icc (A n) (B n) ⊆ (I : Set ℝ))
    (hab : ∀ n, a n ≤ b n) (hAa : ∀ n, A n < a n) (hbB : ∀ n, b n < B n)
    {t c : ℝ} (hc : 0 < c) (hupper : 0 ≤ upper)
    (hwindow : ∀ n, Ioo (t - 113 / 64 * r^2) (t - 111 / 64 * r^2) ⊆ Icc (a n) (b n)) :
    let U : Opens (Fin N → ℝ) := ⟨horizontalBall (G.horizontalFields hq) x (2 * r),
      isOpen_horizontalBall G hq hqpos hspan x (2 * r)⟩
    let η := fun y => max (1 - (horizontalL2Distance (G.horizontalFields hq) x y).toReal /
      (3 * r / 2)) 0
    let D := upper * (((G.homogeneousDimension : ℝ) + 1) *
      ((G.homogeneousDimension : ℝ) + 2)) / (3 * r / 2)^2
    ∃ (g : ℕ → Fin q → ℝ → (Fin N → ℝ) → ℝ) (m : ℕ → ℝ → ℝ),
      (∀ n, WeakSolutionEnergyInterface (G.horizontalFields hq) coeff I U u (g n) ∧
        AbsolutelyContinuousOnInterval (m n) (a n) (b n) ∧
        m n =ᵐ[volume.restrict (Icc (a n) (b n))] (fun s => (∫ y, η y^2)⁻¹ *
          ∫ y, η y^2 * (Real.log (u s y + c) - Real.log c)) ∧
        AbsolutelyContinuousOnInterval (fun s => m n s + D * s) (a n) (b n) ∧
        MonotoneOn (fun s => m n s + D * s) (Icc (a n) (b n)) ∧
        ∀ᵐ s ∂volume.restrict (Icc (a n) (b n)),
          ((∫ y, η y^2)⁻¹ * ∫ y, ∑ i, ∑ j, coeff s y i j *
            (η y * ((u s y + c)⁻¹ * g n j s y)) *
            (η y * ((u s y + c)⁻¹ * g n i s y))) ≤
              2 * deriv (fun z => m n z + D * z) s) ∧
      ∀ᵐ τ ∂volume.restrict (Ioo (t - 113 / 64 * r^2) (t - 111 / 64 * r^2)),
        ∃ shift : ℝ, ∀ n, m n τ = shift := by
  choose g hg m hm hmean hcorr hmono henergy using fun n =>
    hu.exists_logarithmic_tent_mean G hq hqpos hspan hw x hr coeff I ha hlower hbound hu0
      (hJ n) (hab n) (hAa n) (hbB n) hc hupper
  refine ⟨g, m, fun n => ⟨hg n, hm n, hmean n, hcorr n, hmono n, henergy n⟩, ?_⟩
  filter_upwards [ae_common_logarithmic_mean_time hmean hwindow] with τ hτ
  exact ⟨_, hτ⟩

end HeatKernel
