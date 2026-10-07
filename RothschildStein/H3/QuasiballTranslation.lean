-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H3.QuasiballDomain
public import RothschildStein.G2.Algebra

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
open Set
namespace RothschildStein.H3

/-- Translation to the center identifies a quasiball with
its origin-centered counterpart, with the same radius. -/
theorem quasiball_left_pullback {N : ℕ} (G : HomogeneousGroup N)
    (ν : G2.HomogeneousNorm G) (z : Fin N → ℝ) (R : ℝ) :
    G.mul z ⁻¹' (quasiballDomain G ν z R : Set (Fin N → ℝ)) =
      (quasiballDomain G ν 0 R : Set (Fin N → ℝ)) := by
  ext x
  change ν (G.mul (G.inv z) (G.mul z x)) < R ↔ ν (G.mul (G.inv 0) x) < R
  have hz : G.mul (G.inv z) (G.mul z x) = x :=
    (G2.gaugeLeftTranslation G z).left_inv x
  rw [hz, G2.inv_zero, G2.zero_mul]

/-- Pullback by the inverse translation returns the centered ball. -/
theorem quasiball_inverse_left_pullback {N : ℕ} (G : HomogeneousGroup N)
    (ν : G2.HomogeneousNorm G) (z : Fin N → ℝ) (R : ℝ) :
    G.mul (G.inv z) ⁻¹' (quasiballDomain G ν 0 R : Set (Fin N → ℝ)) =
      (quasiballDomain G ν z R : Set (Fin N → ℝ)) := by
  ext x
  change ν (G.mul (G.inv 0) (G.mul (G.inv z) x)) < R ↔
    ν (G.mul (G.inv z) x) < R
  rw [G2.inv_zero, G2.zero_mul]

end RothschildStein.H3
