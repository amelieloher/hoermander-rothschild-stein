-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Moser.HarnackParabolicComparison
public import HeatKernel.Moser.HarnackCoordinateComparison
import Mathlib.Tactic

/-! # Parabolic Harnack inequality on horizontal coordinate balls -/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set MeasureTheory TopologicalSpace RothschildStein
open scoped ENNReal
namespace HeatKernel.Provider

/-- Nonnegative local weak solutions of measurable uniformly elliptic symmetric
matrix equations satisfy the parabolic Harnack inequality on horizontal balls. -/
theorem parabolic_harnack
    {N q : ℕ} (G : HomogeneousGroup N) (hq : q ≤ N) (hqpos : 0 < q)
    (hw : ∀ i : Fin q, G.weight (Fin.castLE hq i) = 1)
    (hspan : bracketSpansOn univ (G.horizontalFields hq))
    (lam Λ : ℝ) (hlam : 0 < lam) (hlamΛ : lam ≤ Λ) :
    let X := G.horizontalFields hq
    let B : (Fin N → ℝ) → ℝ → Set (Fin N → ℝ) :=
      fun x r => {y | horizontalL2Distance X x y < ENNReal.ofReal r}
    ∃ H : ℝ, 1 ≤ H ∧
      ∀ a : ℝ → (Fin N → ℝ) → Fin q → Fin q → ℝ,
        (∀ i j, Measurable (fun z : ℝ × (Fin N → ℝ) => a z.1 z.2 i j)) →
        (∀ᵐ z : ℝ × (Fin N → ℝ) ∂volume,
          (∀ i j, a z.1 z.2 i j = a z.1 z.2 j i) ∧
          ∀ ξ : Fin q → ℝ,
            lam * ∑ i, ξ i ^ 2 ≤ ∑ i, ∑ j, a z.1 z.2 i j * ξ i * ξ j ∧
            ∑ i, ∑ j, a z.1 z.2 i j * ξ i * ξ j ≤ Λ * ∑ i, ξ i ^ 2) →
      ∀ (x : Fin N → ℝ) (r s : ℝ), 0 < r →
      ∀ u : ℝ → (Fin N → ℝ) → ℝ,
        IsLocalWeakSolution G hq hqpos hw hspan a ⟨Ioo (s - 4 * r ^ 2) s, isOpen_Ioo⟩
          ⟨interior (B x (2 * r)), isOpen_interior⟩ u →
        (∀ᵐ z ∂(volume.restrict (Ioo (s - 4 * r ^ 2) s ×ˢ B x (2 * r))), 0 ≤ u z.1 z.2) →
        essSup (fun z : ℝ × (Fin N → ℝ) => ENNReal.ofReal (u z.1 z.2))
            (volume.restrict (Ioo (s - 3 * r ^ 2) (s - 2 * r ^ 2) ×ˢ B x r)) ≤
          ENNReal.ofReal H *
            essInf (fun z : ℝ × (Fin N → ℝ) => ENNReal.ofReal (u z.1 z.2))
              (volume.restrict (Ioo (s - r ^ 2) s ×ˢ B x r)) := by
  obtain ⟨H, hH, hcompare⟩ :=
    HeatKernel.exists_uniform_matrix_parabolic_harnack
      G hq hqpos hspan hw lam Λ hlam (hlam.le.trans hlamΛ)
  exact ⟨H, hH, HeatKernel.parabolic_harnack_of_uniform_cylinder_comparison
    G hq hqpos hw hspan lam Λ H hcompare⟩

end HeatKernel.Provider
