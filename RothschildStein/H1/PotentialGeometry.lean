-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.G2.Gauge
public import RothschildStein.G2.Algebra

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
namespace RothschildStein.H1
variable {N : ℕ} (G : HomogeneousGroup N)

/-- The group-potential decay bound uses the quasi-triangle constant.
The factor two follows from the quasi-triangle inequality (BB printed p. 270). -/
theorem potential_distance_lower (ν : G2.HomogeneousNorm G) {R : ℝ}
    {x y : Fin N → ℝ} (hy : ν y ≤ R) (hx : 2 * ν.c * R ≤ ν x) :
    ν x / (2 * ν.c) ≤ ν (G.mul (G.inv y) x) := by
  have hc : 0 < ν.c := lt_of_lt_of_le (by norm_num) ν.one_le_c
  have ht := ν.mul_le y (G.mul (G.inv y) x)
  rw [← G2.mul_assoc, G2.mul_inv, G2.zero_mul] at ht
  apply (div_le_iff₀ (by positivity : 0 < 2 * ν.c)).mpr
  nlinarith [mul_le_mul_of_nonneg_left hy hc.le]

end RothschildStein.H1
