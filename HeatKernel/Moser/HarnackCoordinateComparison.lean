-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Moser.HarnackUniformComparison
import Mathlib.Tactic

/-! # Parabolic comparison in horizontal coordinate balls

The Carnot metric balls and horizontal control balls are the same sets. The
coordinate and Carnot product measures also agree. These identifications
transfer a uniform cylinder comparison to the coordinate weak-solution class.
-/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set MeasureTheory TopologicalSpace RothschildStein
open scoped ENNReal
namespace HeatKernel
set_option backward.isDefEq.respectTransparency false

/-- A uniform comparison on Carnot metric cylinders gives the coordinate-ball
parabolic comparison with exactly the same constant and coefficient bounds. -/
theorem parabolic_harnack_of_uniform_cylinder_comparison
    {N q : ℕ} (G : HomogeneousGroup N) (hq : q ≤ N) (hqpos : 0 < q)
    (hw : ∀ i : Fin q, G.weight (Fin.castLE hq i) = 1)
    (hspan : bracketSpansOn univ (G.horizontalFields hq))
    (lam Λ H : ℝ)
    (hcompare :
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
          lam * ∑ i, ξ i ^ 2 ≤ ∑ i, ∑ j, coeff z.1 z.2 i j * ξ i * ξ j ∧
          ∑ i, ∑ j, coeff z.1 z.2 i j * ξ i * ξ j ≤ Λ * ∑ i, ξ i ^ 2) →
      let μ := volume.prod (CarnotPoint.volume G hq hqpos hspan)
      essSup (fun y => ENNReal.ofReal (u y)) (μ.restrict (harnackEarlierTargetCylinder x t r)) ≤
        ENNReal.ofReal H *
          essInf (fun y => ENNReal.ofReal (u y)) (μ.restrict (harnackLaterTargetCylinder x t r))) :
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
              (volume.restrict (Ioo (s - r ^ 2) s ×ˢ B x r)) := by
  intro X B a ha hquad x r s hr u hweak hn
  have hU : (⟨interior (B x (2 * r)), isOpen_interior⟩ : Opens (Fin N → ℝ)) =
      ⟨horizontalBall (G.horizontalFields hq) x (2 * r),
        isOpen_horizontalBall G hq hqpos hspan x (2 * r)⟩ := by
    apply Opens.ext
    exact (isOpen_horizontalBall G hq hqpos hspan x (2 * r)).interior_eq
  rw [hU] at hweak
  have hball (ρ : ℝ) :
      (@Metric.ball (CarnotPoint G hq hqpos hspan) _ x ρ : Set (Fin N → ℝ)) = B x ρ :=
    CarnotPoint.coordinateBall_eq_horizontalBall G hq hqpos hspan x ρ
  have hn' : ∀ᵐ z ∂(volume.prod (CarnotPoint.volume G hq hqpos hspan)).restrict
      (Ioo (s - 4 * r ^ 2) s ×ˢ
        @Metric.ball (CarnotPoint G hq hqpos hspan) _ x (2 * r)), 0 ≤ u z.1 z.2 := by
    change ∀ᵐ z ∂(volume : Measure (ℝ × (Fin N → ℝ))).restrict
      (Ioo (s - 4 * r ^ 2) s ×ˢ
        (@Metric.ball (CarnotPoint G hq hqpos hspan) _ x (2 * r) : Set (Fin N → ℝ))),
      0 ≤ u z.1 z.2
    rw [hball]
    exact hn
  have hb := hcompare x s r hr a (fun z => u z.1 z.2) hn' hweak ha hquad
  change essSup (fun z : ℝ × (Fin N → ℝ) => ENNReal.ofReal (u z.1 z.2))
      (volume.restrict (Ioo (s - 3 * r ^ 2) (s - 2 * r ^ 2) ×ˢ
        (@Metric.ball (CarnotPoint G hq hqpos hspan) _ x r : Set (Fin N → ℝ)))) ≤
    ENNReal.ofReal H * essInf (fun z : ℝ × (Fin N → ℝ) => ENNReal.ofReal (u z.1 z.2))
      (volume.restrict (Ioo (s - r ^ 2) s ×ˢ
        (@Metric.ball (CarnotPoint G hq hqpos hspan) _ x r : Set (Fin N → ℝ)))) at hb
  rw [hball] at hb
  exact hb

end HeatKernel
