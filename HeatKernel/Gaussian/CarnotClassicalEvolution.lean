-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Gaussian.SmoothHeatEvolution
public import HeatKernel.Gaussian.SmoothKernelIntegral
public import HeatKernel.Gaussian.CompactNormalizedDatum
import Mathlib.Tactic

/-! # Classical evolutions of normalized Carnot rows

Normalized rows on control balls are compact integrable data. Joint kernel
regularity and the section equation therefore give smooth classical evolutions
in the original coordinates.
-/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open MeasureTheory Set Metric RothschildStein
namespace HeatKernel.Gaussian

/-- The normalized row on a Carnot ball evolves by the classical horizontal
heat equation whenever the coordinate kernel is jointly second-order and
satisfies its section equation. -/
theorem deriv_carnot_normalized_kernel_evolution {N q : ℕ}
    (G : HomogeneousGroup N) (hq : q ≤ N) (hqpos : 0 < q)
    (hspan : bracketSpansOn univ (G.horizontalFields hq))
    (hw : ∀ i : Fin q, G.weight (Fin.castLE hq i) = 1)
    (p : ℝ → (Fin N → ℝ) → (Fin N → ℝ) → ℝ)
    (hp : ContDiffOn ℝ 2 (fun w : ℝ × (Fin N → ℝ) × (Fin N → ℝ) ↦ p w.1 w.2.1 w.2.2)
      (Ioi 0 ×ˢ univ))
    (hheat : ∀ t, 0 < t → ∀ x z, deriv (fun s ↦ p s x z) t =
      sumSquares (G.horizontalFields hq) (fun y ↦ p t y z) x)
    (x y : CarnotPoint G hq hqpos hspan) {r s : ℝ} (hr : 0 < r) (hs : 0 < s)
    (hpos : 0 < ∫ z in ball x r, p s y z ^ 2 ∂(CarnotPoint.volume G hq hqpos hspan)) :
    let μ := CarnotPoint.volume G hq hqpos hspan;
    let g := (ball x r).indicator (fun z ↦ p s y z /
      Real.sqrt (∫ w in ball x r, p s y w ^ 2 ∂μ));
    ∀ σ, 0 < σ → ∀ w : Fin N → ℝ,
      deriv (fun t ↦ ∫ z, g z * p t w z ∂μ) σ =
        sumSquares (G.horizontalFields hq) (fun a ↦ ∫ z, g z * p σ a z ∂μ) w := by
  intro μ g σ hσ w
  have hc : Continuous (p s y) := hp.continuousOn.comp_continuous
    (continuous_const.prodMk (continuous_const.prodMk continuous_id))
    (fun z ↦ ⟨hs, mem_univ (y, z)⟩)
  have hg : Integrable g μ := integrable_carnot_normalized_row G hq hqpos hspan hw x hr
    (p s y) hc.aestronglyMeasurable hpos
  have hcomp : HasCompactSupport (g : (Fin N → ℝ) → ℝ) := hasCompactSupport_carnot_normalized_row G hq hqpos hspan hw x r (p s y)
  exact deriv_integrated_heat_equation_of_contDiff (Z := Fin N → ℝ)
    (volume : Measure (Fin N → ℝ)) hg hcomp (subset_tsupport g)
    (G.horizontalFields hq) (fun i ↦ (G.horizontalFields_contDiff hq i).of_le (by simp))
    p hp hheat hσ w

/-- Jointly smooth coordinate kernels give jointly smooth evolutions of
normalized rows supported on Carnot balls. -/
theorem contDiffOn_carnot_normalized_kernel_evolution {N q : ℕ}
    (G : HomogeneousGroup N) (hq : q ≤ N) (hqpos : 0 < q)
    (hspan : bracketSpansOn univ (G.horizontalFields hq))
    (hw : ∀ i : Fin q, G.weight (Fin.castLE hq i) = 1)
    (p : ℝ → (Fin N → ℝ) → (Fin N → ℝ) → ℝ)
    (hp : ContDiffOn ℝ (⊤ : ℕ∞)
      (fun w : ℝ × (Fin N → ℝ) × (Fin N → ℝ) ↦ p w.1 w.2.1 w.2.2) (Ioi 0 ×ˢ univ))
    (x y : CarnotPoint G hq hqpos hspan) {r s : ℝ} (hr : 0 < r) (hs : 0 < s)
    (hpos : 0 < ∫ z in ball x r, p s y z ^ 2 ∂(CarnotPoint.volume G hq hqpos hspan)) :
    let μ := CarnotPoint.volume G hq hqpos hspan;
    let g := (ball x r).indicator (fun z ↦ p s y z /
      Real.sqrt (∫ w in ball x r, p s y w ^ 2 ∂μ));
    ContDiffOn ℝ (⊤ : ℕ∞) (fun w : ℝ × (Fin N → ℝ) ↦ ∫ z, g z * p w.1 w.2 z ∂μ)
      (Ioi 0 ×ˢ univ) := by
  intro μ g
  have hc : Continuous (p s y) := hp.continuousOn.comp_continuous
    (continuous_const.prodMk (continuous_const.prodMk continuous_id))
    (fun z ↦ ⟨hs, mem_univ (y, z)⟩)
  have hg : Integrable g μ := integrable_carnot_normalized_row G hq hqpos hspan hw x hr
    (p s y) hc.aestronglyMeasurable hpos
  have hcomp : HasCompactSupport (g : (Fin N → ℝ) → ℝ) := hasCompactSupport_carnot_normalized_row G hq hqpos hspan hw x r (p s y)
  have hk : ContDiffOn ℝ (⊤ : ℕ∞)
      (fun w : (ℝ × (Fin N → ℝ)) × (Fin N → ℝ) ↦ p w.1.1 w.1.2 w.2)
      ((Ioi 0 ×ˢ univ) ×ˢ univ) :=
    hp.comp (contDiff_fst.fst.prodMk (contDiff_fst.snd.prodMk contDiff_snd)).contDiffOn
      (fun w hw ↦ ⟨hw.1.1, mem_univ _⟩)
  exact contDiffOn_infty_kernel_integral_of_compact_data (Z := Fin N → ℝ)
    (volume : Measure (Fin N → ℝ)) hg hcomp (subset_tsupport g)
    (isOpen_Ioi.prod isOpen_univ) _ hk

end HeatKernel.Gaussian
