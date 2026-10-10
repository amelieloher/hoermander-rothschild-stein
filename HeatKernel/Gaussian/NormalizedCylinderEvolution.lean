-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Gaussian.CarnotClassicalEvolution
public import HeatKernel.Kernel.ClassicalLocalWeakSolutions

/-! # Normalized heat evolutions on positive cylinders

The classical normalized kernel evolution satisfies the literal local weak
predicate on every open cylinder contained in positive time.
-/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set MeasureTheory Metric RothschildStein TopologicalSpace
namespace HeatKernel.Gaussian

/-- A compact normalized kernel row evolves as a weak heat solution on every
open cylinder whose time interval is positive. -/
theorem isLocalWeakSolution_normalized_kernel_evolution_on_cylinder {N q : ℕ}
    (G : HomogeneousGroup N) (hq : q ≤ N) (hqpos : 0 < q)
    (hspan : bracketSpansOn univ (G.horizontalFields hq))
    (hw : ∀ i : Fin q, G.weight (Fin.castLE hq i) = 1)
    (p : ℝ → (Fin N → ℝ) → (Fin N → ℝ) → ℝ)
    (hp : ContDiffOn ℝ (⊤ : ℕ∞)
      (fun w : ℝ × (Fin N → ℝ) × (Fin N → ℝ) ↦ p w.1 w.2.1 w.2.2) (Ioi 0 ×ˢ univ))
    (hheat : ∀ t, 0 < t → ∀ x z, deriv (fun s ↦ p s x z) t =
      sumSquares (G.horizontalFields hq) (fun y ↦ p t y z) x)
    (x y : CarnotPoint G hq hqpos hspan) {r s : ℝ} (hr : 0 < r) (hs : 0 < s)
    (hpos : 0 < ∫ z in ball x r, p s y z ^ 2 ∂(CarnotPoint.volume G hq hqpos hspan))
    (I : Opens ℝ) (U : Opens (Fin N → ℝ)) (hI : ∀ t ∈ I, 0 < t) :
    let μ := CarnotPoint.volume G hq hqpos hspan;
    let g := (ball x r).indicator (fun z ↦ p s y z /
      Real.sqrt (∫ w in ball x r, p s y w ^ 2 ∂μ));
    IsLocalWeakSolution G hq hqpos hw hspan (fun _ _ i j ↦ if i = j then 1 else 0)
      I U (fun σ w ↦ ∫ z, g z * p σ w z ∂μ) := by
  intro μ g
  have hreg : ContDiffOn ℝ (⊤ : ℕ∞)
      (fun w : ℝ × (Fin N → ℝ) ↦ ∫ z, g z * p w.1 w.2 z ∂μ) (Ioi 0 ×ˢ univ) := by
    simpa [μ, g] using
      contDiffOn_carnot_normalized_kernel_evolution G hq hqpos hspan hw p hp x y hr hs hpos
  apply isLocalWeakSolution_of_smooth_classical_heat_equation G hq hqpos hw hspan I U hI
    (fun σ w ↦ ∫ z, g z * p σ w z ∂μ)
  · convert hreg using 1
    ext w
    simp
  · intro σ hσ w
    exact deriv_carnot_normalized_kernel_evolution G hq hqpos hspan hw p
      (hp.of_le (by simp)) hheat x y hr hs hpos σ hσ w

end HeatKernel.Gaussian
