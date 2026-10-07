-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.G4.ActualChartLocalHomeomorph
public import RothschildStein.G4.ShiftedChartBallInclusions

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set Filter MeasureTheory
open scoped BigOperators

namespace RothschildStein.G4

/-- Actual analytic chart estimates at one original radius. This bundles
proved estimates and does not replace any chart or frame definition. -/
def ChartAnalyticBounds {m n : ℕ} (Ω : Set (Fin n → ℝ)) (w : Fin m → ℕ+)
    (Z : Fin m → (Fin n → ℝ) → (Fin n → ℝ)) (B : Fin n → Fin m)
    (F : (Fin n → ℝ) → (Fin n → ℝ)) (Q : Set (Fin n → ℝ)) (r κ D : ℝ) : Prop :=
  ContDiffOn ℝ (⊤ : ℕ∞) F Q ∧ MapsTo F Q Ω ∧
    (∀ u ∈ Q, Matrix.det (coordinateDerivativeMatrix (fderiv ℝ F u)) ≠ 0) ∧
    (∀ u ∈ Q, frameDet Z B (F u) ≠ 0) ∧
    (∀ u ∈ Q, ∀ j i, |frameCoefficient Z B
      (fun z => fderiv ℝ F u (Pi.single i 1) - Z (B i) z) j (F u)| ≤
        κ * r ^ (((w (B j) : ℕ) : ℤ) - ((w (B i) : ℕ) : ℤ))) ∧
    (∀ u ∈ Q, ∀ J j, |frameCoefficient Z B (Z J) j (F u)| ≤
      D * r ^ (((w (B j) : ℕ) : ℤ) - ((w J : ℕ) : ℤ)))

/-- Actual trajectories for a selected-plus-auxiliary chart, retained as
one family so image and analytic estimates can concern the same chart. -/
def ChartTrajectories {m n : ℕ} (Ω : Set (Fin n → ℝ))
    (Z : Fin m → (Fin n → ℝ) → (Fin n → ℝ)) (B : Fin n → Fin m)
    (F : (Fin n → ℝ) → (Fin n → ℝ)) (Q : Set (Fin n → ℝ))
    (x : Fin n → ℝ) (v : Fin m → ℝ)
    (Γ : (Fin n → ℝ) → ℝ → (Fin n → ℝ)) : Prop :=
  ∀ u ∈ Q, AbsolutelyContinuousOnInterval (Γ u) 0 1 ∧
    MapsTo (Γ u) (Icc (0 : ℝ) 1) Ω ∧ Γ u 0 = x ∧ Γ u 1 = F u ∧
    ∀ᵐ t ∂(volume.restrict (Icc (0 : ℝ) 1)), HasDerivAt (Γ u)
      (∑ j : Fin (n + m), Fin.append u v j • Z (Fin.addCases B id j) (Γ u t)) t

end RothschildStein.G4
