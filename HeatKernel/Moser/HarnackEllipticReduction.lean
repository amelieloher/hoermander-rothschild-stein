-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Moser.EllipticCylinderHarnack
public import HeatKernel.Moser.HarnackCoordinateComparison
import Mathlib.Tactic

/-! # Uniform elliptic comparison from the parabolic comparison

Time-independent coefficients inherit product measurability and ellipticity
from their spatial counterparts. Stationary extension then gives the spatial
comparison with the same constant as the parabolic comparison.
-/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set MeasureTheory TopologicalSpace RothschildStein
open scoped ENNReal
namespace HeatKernel

/-- The uniform coordinate parabolic comparison implies the elliptic
comparison for the same coefficient bounds and the same Harnack constant. -/
theorem elliptic_harnack_of_uniform_parabolic_comparison
    {N q : ℕ} (G : HomogeneousGroup N) (hq : q ≤ N) (hqpos : 0 < q)
    (hw : ∀ i : Fin q, G.weight (Fin.castLE hq i) = 1)
    (hspan : bracketSpansOn univ (G.horizontalFields hq))
    (lam Λ H : ℝ) (hlam : 0 ≤ lam)
    (hparabolic :
      let X := G.horizontalFields hq
      let B : (Fin N → ℝ) → ℝ → Set (Fin N → ℝ) :=
        fun x r => {y | horizontalL2Distance X x y < ENNReal.ofReal r}
      ∀ a : ℝ → (Fin N → ℝ) → Fin q → Fin q → ℝ,
        (∀ i j, Measurable (fun z : ℝ × (Fin N → ℝ) => a z.1 z.2 i j)) →
        (∀ᵐ z : ℝ × (Fin N → ℝ) ∂volume,
          (∀ i j, a z.1 z.2 i j = a z.1 z.2 j i) ∧ ∀ ξ : Fin q → ℝ,
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
                (volume.restrict (Ioo (s - r ^ 2) s ×ˢ B x r))) :
    let X := G.horizontalFields hq
    let B : (Fin N → ℝ) → ℝ → Set (Fin N → ℝ) :=
      fun x r => {y | horizontalL2Distance X x y < ENNReal.ofReal r}
    ∀ a : (Fin N → ℝ) → Fin q → Fin q → ℝ,
      (∀ i j, Measurable (fun x => a x i j)) →
      (∀ᵐ x ∂volume,
        (∀ i j, a x i j = a x j i) ∧ ∀ ξ : Fin q → ℝ,
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
          ENNReal.ofReal H * essInf (fun y => ENNReal.ofReal (u y))
            (volume.restrict (B x r)) := by
  intro X B a ha hquad x r hr U u hu hell hn
  have hameas (i j : Fin q) :
      Measurable (fun z : ℝ × (Fin N → ℝ) => a z.2 i j) :=
    (ha i j).comp measurable_snd
  have hquadtime : ∀ᵐ z : ℝ × (Fin N → ℝ) ∂volume,
      (∀ i j, a z.2 i j = a z.2 j i) ∧ ∀ ξ : Fin q → ℝ,
        lam * ∑ i, ξ i ^ 2 ≤ ∑ i, ∑ j, a z.2 i j * ξ i * ξ j ∧
        ∑ i, ∑ j, a z.2 i j * ξ i * ξ j ≤ Λ * ∑ i, ξ i ^ 2 := by
    have hb := (Measure.quasiMeasurePreserving_snd
      (μ := (volume : Measure ℝ)) (ν := (volume : Measure (Fin N → ℝ)))).ae hquad
    simpa only [← Measure.volume_eq_prod] using hb
  exact elliptic_harnack_of_cylinder_harnack_estimate G hq hqpos hw hspan a
    (B x (2 * r)) (B x r) r 0 lam Λ H hr hlam ha hquad
    (fun w hwweak hwpos =>
      hparabolic (fun _ y => a y) hameas hquadtime x r 0 hr w hwweak hwpos)
    hu hell hn

end HeatKernel
