-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Form.ZeroBoundaryCore
public import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Tactic.Linter

/-! # The stationary energy-test identity on compact interior cylinders -/

@[expose] public section
open Set MeasureTheory TopologicalSpace
namespace HeatKernel

/-- The literal value and flux pairings with all stationary zero-boundary form tests,
after arbitrary smooth temporal localization on a compact interior cylinder. -/
def HasStationaryEnergyTestIdentity {N q : ℕ}
    (X : Fin q → (Fin N → ℝ) → (Fin N → ℝ))
    (a : ℝ → (Fin N → ℝ) → Fin q → Fin q → ℝ) (I : Opens ℝ) (U : Opens (Fin N → ℝ))
    (u : ℝ → (Fin N → ℝ) → ℝ) (g : Fin q → ℝ → (Fin N → ℝ) → ℝ) : Prop :=
      ∀ (J : Set ℝ) (K : Set (Fin N → ℝ)),
        IsCompact J → J ⊆ (I : Set ℝ) → IsCompact K → K ⊆ (U : Set (Fin N → ℝ)) →
      ∀ (V : Opens (Fin N → ℝ)), (V : Set (Fin N → ℝ)) ⊆ K →
      ∀ (ψ : ℝ → ℝ), ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ → tsupport ψ ⊆ J →
      ∀ v : zeroBoundaryGraph V (X),
        Integrable (fun z : ℝ × (Fin N → ℝ) =>
          (-(deriv ψ z.1) * u z.1 z.2) * (v : GradientSpace (N := N) ⊤ q).fst z.2)
          ((volume.restrict J).prod volume) ∧
        (∀ i, Integrable (fun z : ℝ × (Fin N → ℝ) =>
          (ψ z.1 * ∑ j, a z.1 z.2 i j * g j z.1 z.2) *
            (v : GradientSpace (N := N) ⊤ q).snd i z.2) ((volume.restrict J).prod volume)) ∧
        (∫ z : ℝ × (Fin N → ℝ), (-(deriv ψ z.1) * u z.1 z.2) *
          (v : GradientSpace (N := N) ⊤ q).fst z.2 ∂(volume.restrict J).prod volume) +
          (∑ i, ∫ z : ℝ × (Fin N → ℝ),
            (ψ z.1 * ∑ j, a z.1 z.2 i j * g j z.1 z.2) *
              (v : GradientSpace (N := N) ⊤ q).snd i z.2 ∂(volume.restrict J).prod volume) = 0

end HeatKernel
