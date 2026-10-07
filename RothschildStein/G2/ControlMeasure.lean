-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.G2.ControlTransport
public import RothschildStein.G2.HomogeneousType

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false

@[expose] public section
noncomputable section
namespace RothschildStein.G2
open Set MeasureTheory
variable {N m : ℕ} (G : HomogeneousGroup N)

/-- A homogeneous norm represents the weighted control distance with unit constant and symmetry (BB Theorem 3.54, pp. 125–127). -/
structure ControlNormConclusion (w : Fin m → ℕ+)
    (X : Fin m → (Fin N → ℝ) → (Fin N → ℝ)) where
  norm : HomogeneousNorm G
  constant_one : norm.c = 1
  symmetric : norm.Symmetric
  distance_eq : ∀ x y, controlDistance univ w X x y = ENNReal.ofReal (gaugeDistance G norm x y)

/-- Given a norm representation, the real control distance equals its gauge distance (BB Theorem 3.54, p. 126). -/
theorem controlDistance_toReal_of_controlNorm {w : Fin m → ℕ+}
    {X : Fin m → (Fin N → ℝ) → (Fin N → ℝ)}
    (H : ControlNormConclusion G w X) (x y : Fin N → ℝ) :
    (controlDistance univ w X x y).toReal = gaugeDistance G H.norm x y := by
  rw [H.distance_eq]
  apply ENNReal.toReal_ofReal
  exact H.norm.gauge.2.1 _

end RothschildStein.G2
