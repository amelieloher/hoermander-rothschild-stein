-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H3.SmoothGaugeCutoff
public import RothschildStein.G2.Foundation

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
namespace RothschildStein.H3

/-- The fixed unit profile shared by the near and far kernels. -/
def interpolationCutoffProfile : ℝ → ℝ := quasiballProfile (1 / 2) 1

/-- The common profile is smooth. -/
theorem interpolationCutoffProfile_smooth :
    ContDiff ℝ (⊤ : ℕ∞) interpolationCutoffProfile := quasiballProfile_contDiff _ _

/-- The common profile equals one below one half. -/
theorem interpolationCutoffProfile_one {t : ℝ} (ht : t ≤ 1 / 2) :
    interpolationCutoffProfile t = 1 := quasiballProfile_one (by norm_num) ht

/-- The common profile vanishes above one. -/
theorem interpolationCutoffProfile_zero {t : ℝ} (ht : 1 ≤ t) :
    interpolationCutoffProfile t = 0 := quasiballProfile_zero (by norm_num) (by linarith)

/-- Exact inverse-scale identity for the half-radius profile. -/
theorem quasiballProfile_half_scale {ε : ℝ} (hε : 0 < ε) (t : ℝ) :
    quasiballProfile (ε / 2) ε t = interpolationCutoffProfile (t / ε) := by
  unfold interpolationCutoffProfile quasiballProfile
  congr 1
  field_simp [hε.ne']

/-- The actual constructed near cutoff is the radial common
profile, so its complement is the exterior kernel's exact cutoff. -/
theorem near_cutoff_eq_interpolation_profile {N : ℕ} (G : HomogeneousGroup N)
    (ν : G2.HomogeneousNorm G) {ε : ℝ} (hε : 0 < ε) (x : Fin N → ℝ) :
    smoothQuasiballCutoff G ν 0 (ε / 2) ε x = interpolationCutoffProfile (ν x / ε) := by
  unfold smoothQuasiballCutoff
  rw [G2.inv_zero G, G2.zero_mul G]
  exact quasiballProfile_half_scale hε _

end RothschildStein.H3
