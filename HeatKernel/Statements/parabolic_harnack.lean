-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import Mathlib
public import RothschildStein.Definitions.HomogeneousGroup
public import RothschildStein.Definitions.HomogeneousGroup.horizontalFields
public import RothschildStein.Definitions.bracketSpansOn
public import HeatKernel.Definitions.horizontalL2Distance
public import HeatKernel.Definitions.IsLocalWeakSolution
public import HeatKernel.Provider.parabolic_harnack

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set MeasureTheory TopologicalSpace Filter
open scoped BigOperators Topology ENNReal NNReal

namespace HeatKernel

open RothschildStein

/-- Parabolic Harnack inequality for measurable uniformly elliptic symmetric coefficients
(Saloff-Coste 1992, Theorem 3.1): there is `H ≥ 1`, depending only on the group, its horizontal
fields and the ellipticity bounds `0 < lam ≤ Λ`, such that every nonnegative local weak solution
of `∂ₜu = ∑ᵢⱼ Xᵢ(aᵢⱼ Xⱼ u)` on `(s - 4r², s) × B(x, 2r)` satisfies
`ess sup_{(s - 3r², s - 2r²) × B(x, r)} u ≤ H · ess inf_{(s - r², s) × B(x, r)} u`. Balls are open
balls of the horizontal `ℓ²`-control distance `horizontalL2Distance X`. -/
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
              (volume.restrict (Ioo (s - r ^ 2) s ×ˢ B x r)) :=
  by exact HeatKernel.Provider.parabolic_harnack G hq hqpos hw hspan lam Λ hlam hlamΛ

end HeatKernel
