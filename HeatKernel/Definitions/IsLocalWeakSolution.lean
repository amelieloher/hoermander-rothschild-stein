-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import Mathlib
public import RothschildStein.Definitions.HomogeneousGroup
public import RothschildStein.Definitions.HomogeneousGroup.horizontalFields
public import RothschildStein.Definitions.bracketSpansOn
public import RothschildStein.Definitions.hasWeakWordDeriv

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set MeasureTheory TopologicalSpace Filter
open scoped BigOperators Topology ENNReal NNReal

namespace HeatKernel

open RothschildStein

/-- `u` is a local weak solution of the forward equation `∂ₜu = ∑ᵢⱼ Xᵢ(aᵢⱼ Xⱼ u)` on the
cylinder `I × U`, where `X₁, …, X_q` are the weight-one horizontal fields
`G.horizontalFields hq` of a Carnot group: the carrier is the Carnot-group data only (for these
divergence-free fields the weak identity below is the forward equation). The function `u` is
jointly measurable on `I × U`; there is a horizontal gradient `g`, which for almost every time is the
weak gradient `(X₁ u(t), …, X_q u(t))` on `U`; on every compact `J × K ⊆ I × U`,
`u ∈ L^∞(J; L²(K))` and `g ∈ L²(J × K)`; and for every smooth test function `φ` compactly supported
in `I × U`, `∫∫ (-u ∂ₜφ + ∑ᵢⱼ aᵢⱼ (Xⱼ u) (Xᵢ φ)) = 0`, with an integrable integrand. -/
def IsLocalWeakSolution {N q : ℕ}
    (G : HomogeneousGroup N) (hq : q ≤ N) (_hqpos : 0 < q)
    (_hw : ∀ i : Fin q, G.weight (Fin.castLE hq i) = 1)
    (_hspan : bracketSpansOn univ (G.horizontalFields hq))
    (a : ℝ → (Fin N → ℝ) → Fin q → Fin q → ℝ)
    (I : Opens ℝ) (U : Opens (Fin N → ℝ))
    (u : ℝ → (Fin N → ℝ) → ℝ) : Prop :=
  let X := G.horizontalFields hq
  AEStronglyMeasurable (fun z : ℝ × (Fin N → ℝ) => u z.1 z.2)
    (volume.restrict ((I : Set ℝ) ×ˢ (U : Set (Fin N → ℝ)))) ∧
  ∃ g : Fin q → ℝ → (Fin N → ℝ) → ℝ,
    (∀ᵐ t ∂(volume.restrict (I : Set ℝ)), ∀ i, hasWeakWordDeriv X U [i] (u t) (g i t)) ∧
    (∀ (J : Set ℝ) (K : Set (Fin N → ℝ)),
      IsCompact J → J ⊆ (I : Set ℝ) → IsCompact K → K ⊆ (U : Set (Fin N → ℝ)) →
      essSup (fun t => eLpNorm (u t) 2 (volume.restrict K)) (volume.restrict J) < ⊤ ∧
      ∀ i, MemLp (fun z : ℝ × (Fin N → ℝ) => g i z.1 z.2) 2 (volume.restrict (J ×ˢ K))) ∧
    ∀ φ : ℝ × (Fin N → ℝ) → ℝ,
      ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
      tsupport φ ⊆ (I : Set ℝ) ×ˢ (U : Set (Fin N → ℝ)) →
      Integrable (fun z : ℝ × (Fin N → ℝ) =>
        -(u z.1 z.2 * fderiv ℝ φ z (1, 0)) +
          ∑ i, ∑ j, a z.1 z.2 i j * g j z.1 z.2 * fderiv ℝ φ z (0, X i z.2)) ∧
      ∫ z : ℝ × (Fin N → ℝ),
        (-(u z.1 z.2 * fderiv ℝ φ z (1, 0)) +
          ∑ i, ∑ j, a z.1 z.2 i j * g j z.1 z.2 * fderiv ℝ φ z (0, X i z.2)) = 0

end HeatKernel
