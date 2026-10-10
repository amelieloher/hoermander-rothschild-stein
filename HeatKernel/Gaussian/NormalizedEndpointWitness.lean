-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Gaussian.NormalizedCylinderEvolution
public import HeatKernel.Kernel.KernelStrongContinuity
public import HeatKernel.Gaussian.NormalizedKernelEvolution

/-! # Represented smooth normalized endpoint evolutions

One literal normalized kernel integral supplies the L² representation,
smoothness, central square identity, and local weak solution on positive cylinders.
-/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set MeasureTheory Metric RothschildStein TopologicalSpace
namespace HeatKernel.Gaussian

/-- Normalized compact kernel rows have a common represented smooth evolution
with the exact central square and weak-solution properties. -/
theorem exists_represented_normalized_endpoint_evolution {N q : ℕ}
    (G : HomogeneousGroup N) (hq : q ≤ N) (hqpos : 0 < q)
    (hspan : bracketSpansOn univ (G.horizontalFields hq))
    (hw : ∀ i : Fin q, G.weight (Fin.castLE hq i) = 1)
    (p : ℝ → (Fin N → ℝ) → (Fin N → ℝ) → ℝ)
    (hp : ContDiffOn ℝ (⊤ : ℕ∞)
      (fun w : ℝ × (Fin N → ℝ) × (Fin N → ℝ) ↦ p w.1 w.2.1 w.2.2) (Ioi 0 ×ˢ univ))
    (hheat : ∀ t, 0 < t → ∀ x z, deriv (fun s ↦ p s x z) t =
      sumSquares (G.horizontalFields hq) (fun y ↦ p t y z) x)
    (hn : ∀ σ, 0 < σ → ∀ w z, 0 ≤ p σ w z)
    (T : ℝ → Lp ℝ 2 (CarnotPoint.volume G hq hqpos hspan) →L[ℝ]
      Lp ℝ 2 (CarnotPoint.volume G hq hqpos hspan))
    (hrepr : ∀ σ > 0, ∀ u : Lp ℝ 2 (CarnotPoint.volume G hq hqpos hspan),
      (fun w ↦ ∫ z, p σ w z * u z ∂(CarnotPoint.volume G hq hqpos hspan)) =ᵐ[
        CarnotPoint.volume G hq hqpos hspan] T σ u)
    (x y : CarnotPoint G hq hqpos hspan) {r s : ℝ} (hr : 0 < r) (hs : 0 < s)
    (hpos : 0 < ∫ z in ball x r, p s y z ^ 2 ∂(CarnotPoint.volume G hq hqpos hspan)) :
    let μ := CarnotPoint.volume G hq hqpos hspan;
    let A := ∫ z in ball x r, p s y z ^ 2 ∂μ;
    ∃ u : Lp ℝ 2 μ,
      u =ᵐ[μ] (ball x r).indicator (fun z ↦ p s y z / Real.sqrt A) ∧
    ∃ v : ℝ × (Fin N → ℝ) → ℝ,
      ContDiffOn ℝ (⊤ : ℕ∞) v (Ioi 0 ×ˢ univ) ∧
      (∀ σ > 0, (fun z ↦ v (σ, z)) =ᵐ[μ] T σ u) ∧
      v (s, y) ^ 2 = A ∧
      (∀ σ > 0, ∀ w, 0 ≤ v (σ, w)) ∧
      ∀ (I : Opens ℝ) (U : Opens (Fin N → ℝ)), (∀ σ ∈ I, 0 < σ) →
        IsLocalWeakSolution G hq hqpos hw hspan (fun _ _ i j ↦ if i = j then 1 else 0)
          I U (fun σ w ↦ v (σ, w)) := by
  intro μ A
  have hc : Continuous (p s y) := hp.continuousOn.comp_continuous
    (continuous_const.prodMk (continuous_const.prodMk continuous_id))
    (fun z ↦ ⟨hs, mem_univ _⟩)
  have hf : AEStronglyMeasurable (p s y) μ := hc.aestronglyMeasurable
  let g := (ball x r).indicator (fun z ↦ p s y z / Real.sqrt A)
  let u := (memLp_normalized_indicator μ measurableSet_ball (p s y) hf hpos).toLp g
  let v := fun w : ℝ × (Fin N → ℝ) ↦ ∫ z, g z * p w.1 w.2 z ∂μ
  refine ⟨u, (memLp_normalized_indicator μ measurableSet_ball (p s y) hf hpos).coeFn_toLp,
    v, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [v, g, μ, A] using
      contDiffOn_carnot_normalized_kernel_evolution G hq hqpos hspan hw p hp x y hr hs hpos
  · intro σ hσ
    have hu : u =ᵐ[μ] g :=
      (memLp_normalized_indicator μ measurableSet_ball (p s y) hf hpos).coeFn_toLp
    have he : (fun w ↦ v (σ, w)) = (fun w ↦ ∫ z, p σ w z * u z ∂μ) := by
      funext w
      apply integral_congr_ae
      filter_upwards [hu] with z hz
      rw [hz, mul_comm]
    rw [he]
    exact hrepr σ hσ u
  · have he : v (s, y) = Real.sqrt A := by
      simpa only [v, g, A, mul_comm] using
        integral_kernel_normalized_row_eq_sqrt μ measurableSet_ball p s y hpos
    rw [he, Real.sq_sqrt hpos.le]
  · intro σ hσ w
    simpa only [v, g, A, mul_comm] using
      integral_kernel_normalized_row_nonneg μ (ball x r) p hn hs hσ w y
  · intro I U hI
    exact isLocalWeakSolution_normalized_kernel_evolution_on_cylinder G hq hqpos hspan hw
      p hp hheat x y hr hs hpos I U hI

end HeatKernel.Gaussian
