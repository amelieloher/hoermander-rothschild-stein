-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module
public import RothschildStein.G3.Grading
@[expose] public section
noncomputable section
namespace RothschildStein.G3

theorem norm_weightProjection_le {a s : ℕ} {p : Fin a → ℕ+}
    (k : ℕ) (f : WordCoefficients a s p) : ‖weightProjection k f‖ ≤ ‖f‖ := by
  apply (pi_norm_le_iff_of_nonneg (norm_nonneg f)).mpr
  intro I
  change ‖if wordWeight p I.val = k then f I else 0‖ ≤ ‖f‖
  split
  · exact norm_le_pi_norm f I
  · simpa only [norm_zero] using norm_nonneg f
end RothschildStein.G3
