-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.L1.FixedLiftData
public import RothschildStein.L1.TriangularBallProjection
public import RothschildStein.L1.PrefixDerivative
public import RothschildStein.L1.TriangularBracketProjection
public import RothschildStein.G4.AuxiliaryControl

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set
open scoped ENNReal
namespace RothschildStein.L1.FixedLiftData

/-- The fixed lift projects every ambient ordinary ball exactly,
with the polynomial chosen before the center and radius. -/
theorem rsBall_projection_eq {n k s m : ℕ} {w : Fin k → ℕ+}
    {Ω : Set (Fin n → ℝ)} {X : Fin k → (Fin n → ℝ) → (Fin n → ℝ)}
    {x₀ : Fin n → ℝ} (L : FixedLiftData w s Ω X x₀ m) (hΩ : IsOpen Ω)
    (η : Fin (n+m) → ℝ) (r : ℝ) :
    basePoint '' rsBall (basePoint ⁻¹' Ω) w (triangularLift X L.P) η r =
      rsBall Ω w X (basePoint η) r :=
  rsBall_triangularLift_projection_eq hΩ w X L.P L.vars_lt η r

/-- The distance clause of the ball projection needs no geometric premise. -/
theorem controlDistance_projection_le {n k s m : ℕ} {w : Fin k → ℕ+}
    {Ω : Set (Fin n → ℝ)} {X : Fin k → (Fin n → ℝ) → (Fin n → ℝ)}
    {x₀ : Fin n → ℝ} (L : FixedLiftData w s Ω X x₀ m) (hΩ : IsOpen Ω)
    (η ξ : Fin (n+m) → ℝ) :
    controlDistance Ω w X (basePoint η) (basePoint ξ) ≤
      controlDistance (basePoint ⁻¹' Ω) w (triangularLift X L.P) η ξ :=
  controlDistance_triangularLift_projection_le hΩ w X L.P η ξ

end RothschildStein.L1.FixedLiftData
