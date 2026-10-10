-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Moser.StationaryFluxTests
public import HeatKernel.Form.MatrixCoefficientBounds

/-! # Stationary uniformly elliptic solutions

Symmetric ellipticity bounds control each matrix entry. The resulting bounded fluxes
place stationary local elliptic solutions in the parabolic weak solution class.
-/

@[expose] public section

open Set MeasureTheory Filter TopologicalSpace RothschildStein
open scoped BigOperators

namespace HeatKernel

/-- The local elliptic weak formulation with symmetric uniformly elliptic measurable
coefficients gives a stationary local weak parabolic solution on every time interval. -/
theorem isLocalWeakSolution_stationary_of_ellipticity {N q : ℕ}
    (G : HomogeneousGroup N) (hq : q ≤ N) (hqpos : 0 < q)
    (hw : ∀ i : Fin q, G.weight (Fin.castLE hq i) = 1)
    (hspan : bracketSpansOn univ (G.horizontalFields hq))
    (a : (Fin N → ℝ) → Fin q → Fin q → ℝ)
    (I : Opens ℝ) (U : Opens (Fin N → ℝ)) (lam Λ : ℝ) (hlam : 0 ≤ lam)
    (ha : ∀ i j, Measurable (fun x => a x i j))
    (hb : ∀ᵐ x ∂volume, (∀ i j, a x i j = a x j i) ∧
      ∀ ξ : Fin q → ℝ,
        lam * ∑ i, ξ i ^ 2 ≤ ∑ i, ∑ j, a x i j * ξ i * ξ j ∧
        ∑ i, ∑ j, a x i j * ξ i * ξ j ≤ Λ * ∑ i, ξ i ^ 2)
    {u : (Fin N → ℝ) → ℝ}
    (hu : memSobolevXLoc noDriftWeight (G.horizontalFields hq) U 1 2 u)
    (hell : ∃ g : Fin q → (Fin N → ℝ) → ℝ,
      (∀ i, hasWeakWordDeriv (G.horizontalFields hq) U [i] u (g i)) ∧
      ∀ ψ : TestFunction U ℝ (⊤ : ℕ∞),
        (∫ x in (U : Set (Fin N → ℝ)),
          ∑ i, ∑ j, a x i j * g j x * fieldDerivative (G.horizontalFields hq i) ψ x) = 0) :
    IsLocalWeakSolution G hq hqpos hw hspan (fun _ x => a x) I U (fun _ x => u x) := by
  obtain ⟨g, hg, he⟩ := hell
  have hbound : ∀ i j, ∀ᵐ x ∂volume, ‖a x i j‖ ≤ Λ := by
    intro i j
    filter_upwards [hb] with x hx
    apply norm_matrix_entry_le_of_elliptic_bounds (a x) hlam hx.1 _ i j
    intro ξ
    have hm : matrixEnergy (a x) ξ = ∑ i, ∑ j, a x i j * ξ i * ξ j := by
      unfold matrixEnergy
      apply Finset.sum_congr rfl
      intro k _
      apply Finset.sum_congr rfl
      intro l _
      ring
    simpa only [hm, coordinateNormSq] using hx.2 ξ
  exact isLocalWeakSolution_stationary_of_bounded_coefficients
    G hq hqpos hw hspan a I U hu hg ha hbound he

end HeatKernel
