-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Bridge.DualEnergyPair
public import HeatKernel.Form.ZeroBoundary

/-! # Dual energy identities on compact interior cylinders -/

@[expose] public section
open Set MeasureTheory TopologicalSpace
namespace HeatKernel

/-- On each compact interior cylinder the value and horizontal flux have
square-integrable form-dual representatives satisfying the weak time equation. -/
def HasLocalDualEnergyCurves {N q : ℕ}
    (X : Fin q → (Fin N → ℝ) → (Fin N → ℝ))
    (a : ℝ → (Fin N → ℝ) → Fin q → Fin q → ℝ)
    (I : Opens ℝ) (U : Opens (Fin N → ℝ))
    (u : ℝ → (Fin N → ℝ) → ℝ) (g : Fin q → ℝ → (Fin N → ℝ) → ℝ) : Prop :=
  ∀ (J : Set ℝ) (K : Set (Fin N → ℝ)),
    IsCompact J → J ⊆ (I : Set ℝ) → IsCompact K → K ⊆ (U : Set (Fin N → ℝ)) →
    ∀ (V : Opens (Fin N → ℝ)), (V : Set (Fin N → ℝ)) ⊆ K →
    ∃ D F : ℝ → (zeroBoundaryGraph V X →L[ℝ] ℝ),
      IsDualEnergyPair (E := zeroBoundaryGraph V X) J
        (fun t v => ∫ x, u t x * (v : GradientSpace (N := N) ⊤ q).fst x)
        (fun t v => ∑ i, ∫ x, (∑ j, a t x i j * g j t x) *
          (v : GradientSpace (N := N) ⊤ q).snd i x) D F

end HeatKernel
