-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Provider.parabolic_harnack
public import HeatKernel.Moser.HarnackEllipticReduction
import Mathlib.Tactic

/-! # Elliptic Harnack inequality on horizontal coordinate balls

Stationary extension transfers the parabolic comparison to elliptic weak
solutions, preserving the normalized Harnack constant.
-/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set MeasureTheory TopologicalSpace RothschildStein
open scoped ENNReal
namespace HeatKernel.Provider

/-- Nonnegative local elliptic weak solutions with measurable uniformly
elliptic symmetric coefficients satisfy Harnack on horizontal balls. -/
theorem elliptic_harnack
    {N q : ℕ} (G : HomogeneousGroup N) (hq : q ≤ N) (hqpos : 0 < q)
    (hw : ∀ i : Fin q, G.weight (Fin.castLE hq i) = 1)
    (hspan : bracketSpansOn univ (G.horizontalFields hq))
    (lam Λ : ℝ) (hlam : 0 < lam) (hlamΛ : lam ≤ Λ) :
    let X := G.horizontalFields hq
    let B : (Fin N → ℝ) → ℝ → Set (Fin N → ℝ) :=
      fun x r => {y | horizontalL2Distance X x y < ENNReal.ofReal r}
    ∃ H : ℝ, 1 ≤ H ∧
      ∀ a : (Fin N → ℝ) → Fin q → Fin q → ℝ,
        (∀ i j, Measurable (fun x => a x i j)) →
        (∀ᵐ x ∂volume,
          (∀ i j, a x i j = a x j i) ∧
          ∀ ξ : Fin q → ℝ,
            lam * ∑ i, ξ i ^ 2 ≤ ∑ i, ∑ j, a x i j * ξ i * ξ j ∧
            ∑ i, ∑ j, a x i j * ξ i * ξ j ≤ Λ * ∑ i, ξ i ^ 2) →
      ∀ (x : Fin N → ℝ) (r : ℝ), 0 < r →
      let U : Opens (Fin N → ℝ) := ⟨interior (B x (2 * r)), isOpen_interior⟩
      ∀ u : (Fin N → ℝ) → ℝ,
        memSobolevXLoc noDriftWeight X U 1 2 u →
        (∃ g : Fin q → (Fin N → ℝ) → ℝ,
          (∀ i, hasWeakWordDeriv X U [i] u (g i)) ∧
          ∀ φ : TestFunction U ℝ (⊤ : ℕ∞),
            ∫ y in (U : Set (Fin N → ℝ)),
              ∑ i, ∑ j, a y i j * g j y * fieldDerivative (X i) φ y = 0) →
        (∀ᵐ y ∂(volume.restrict (B x (2 * r))), 0 ≤ u y) →
        essSup (fun y => ENNReal.ofReal (u y)) (volume.restrict (B x r)) ≤
          ENNReal.ofReal H * essInf (fun y => ENNReal.ofReal (u y)) (volume.restrict (B x r)) := by
  obtain ⟨H, hH, hparabolic⟩ :=
    HeatKernel.Provider.parabolic_harnack G hq hqpos hw hspan lam Λ hlam hlamΛ
  exact ⟨H, hH, HeatKernel.elliptic_harnack_of_uniform_parabolic_comparison
    G hq hqpos hw hspan lam Λ H hlam.le hparabolic⟩

end HeatKernel.Provider
