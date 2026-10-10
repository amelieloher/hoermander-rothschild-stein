-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Moser.HolderCylinderOscillation
public import HeatKernel.Moser.HarnackParabolicComparison
public import HeatKernel.Moser.HarnackCoordinateComparison

/-! # Uniform oscillation decay for elliptic matrix weak equations -/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set MeasureTheory TopologicalSpace RothschildStein Filter
namespace HeatKernel

/-- Uniformly elliptic matrix weak solutions have a strict uniform contraction
of essential oscillation from the outer cylinder to its later half-radius
cylinder. The factor depends only on the group, frame and ellipticity bounds. -/
theorem exists_uniform_matrix_oscillation_decay {N q : ℕ}
    (G : HomogeneousGroup N) (hq : q ≤ N) (hqpos : 0 < q)
    (hspan : bracketSpansOn univ (G.horizontalFields hq))
    (hw : ∀ i : Fin q, G.weight (Fin.castLE hq i) = 1)
    (ell upper : ℝ) (hell : 0 < ell) (hupper : 0 ≤ upper) :
    ∃ θ : ℝ, θ ∈ Ioo (0 : ℝ) 1 ∧
      ∀ a : ℝ → (Fin N → ℝ) → Fin q → Fin q → ℝ,
      (∀ i j, Measurable (fun z : ℝ × (Fin N → ℝ) => a z.1 z.2 i j)) →
      (∀ᵐ z : ℝ × (Fin N → ℝ) ∂volume,
        (∀ i j, a z.1 z.2 i j = a z.1 z.2 j i) ∧ ∀ ξ : Fin q → ℝ,
          ell * ∑ i, ξ i ^ 2 ≤ ∑ i, ∑ j, a z.1 z.2 i j * ξ i * ξ j ∧
          ∑ i, ∑ j, a z.1 z.2 i j * ξ i * ξ j ≤ upper * ∑ i, ξ i ^ 2) →
      ∀ (x : Fin N → ℝ) (t r : ℝ), 0 < r →
      ∀ u : ℝ → (Fin N → ℝ) → ℝ,
      IsLocalWeakSolution G hq hqpos hw hspan a
      ⟨Ioo (t - 4 * r ^ 2) t, isOpen_Ioo⟩
      ⟨horizontalBall (G.horizontalFields hq) x (2 * r),
        isOpen_horizontalBall G hq hqpos hspan x (2 * r)⟩ u →
      IsBoundedUnder (· ≤ ·)
      (ae (volume.restrict (Ioo (t - 4 * r ^ 2) t ×ˢ
        horizontalBall (G.horizontalFields hq) x (2 * r)))) (Function.uncurry u) →
      IsBoundedUnder (· ≥ ·)
      (ae (volume.restrict (Ioo (t - 4 * r ^ 2) t ×ˢ
        horizontalBall (G.horizontalFields hq) x (2 * r)))) (Function.uncurry u) →
    essSup (Function.uncurry u)
        (volume.restrict (Ioo (t - r ^ 2) t ×ˢ horizontalBall (G.horizontalFields hq) x r)) -
      essInf (Function.uncurry u)
        (volume.restrict (Ioo (t - r ^ 2) t ×ˢ horizontalBall (G.horizontalFields hq) x r)) ≤
      θ *
        (essSup (Function.uncurry u)
            (volume.restrict (Ioo (t - 4 * r ^ 2) t ×ˢ horizontalBall (G.horizontalFields hq) x (2 * r))) -
          essInf (Function.uncurry u)
            (volume.restrict (Ioo (t - 4 * r ^ 2) t ×ˢ horizontalBall (G.horizontalFields hq) x (2 * r)))) := by
  obtain ⟨H, hH, hcompare⟩ :=
    exists_uniform_matrix_parabolic_harnack G hq hqpos hspan hw ell upper hell hupper
  have hcoord := parabolic_harnack_of_uniform_cylinder_comparison
    G hq hqpos hw hspan ell upper H hcompare
  refine ⟨1 - 1 / (2 * H), harnack_oscillation_factor_mem_Ioo hH, ?_⟩
  intro a ha hquad x t r hr u hu hhi hlo
  apply (IsLocalWeakSolution.essential_oscillation_on_cylinder_le_of_harnack
    G hq hqpos hw hspan x t r H hr hH a ?_ hu hhi hlo).2
  intro w hweak hn
  apply hcoord a ha hquad x r t hr w ?_ hn
  have hball := (isOpen_horizontalBall G hq hqpos hspan x (2 * r)).interior_eq
  change IsLocalWeakSolution G hq hqpos hw hspan a
    ⟨Ioo (t - 4 * r ^ 2) t, isOpen_Ioo⟩
    ⟨interior (horizontalBall (G.horizontalFields hq) x (2 * r)), isOpen_interior⟩ w
  have hU : (⟨interior (horizontalBall (G.horizontalFields hq) x (2 * r)),
      isOpen_interior⟩ : Opens (Fin N → ℝ)) =
      ⟨horizontalBall (G.horizontalFields hq) x (2 * r),
        isOpen_horizontalBall G hq hqpos hspan x (2 * r)⟩ := Opens.ext hball
  rw [hU]
  exact hweak

end HeatKernel
