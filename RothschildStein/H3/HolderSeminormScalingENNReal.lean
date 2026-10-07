-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H3.HolderSeminormScalingLimit
public import Mathlib.Basic.ENNReal.Real

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
namespace RothschildStein.H3
open scoped ENNReal

/-- The large-scale limit for finite extended Hölder
quantities, preserving the norm API's extended-real values (BB p. 380). -/
theorem holder_seminorm_bound_of_scaled_ennreal_full_norm_bound
    {α R0 c : ℝ} (hα : 0 < α) (hc : 0 ≤ c)
    {A B S T : ℝ≥0∞} (hA : A ≠ ⊤) (hB : B ≠ ⊤)
    (hS : S ≠ ⊤) (hT : T ≠ ⊤)
    (hscale : ∀ R : ℝ, R0 ≤ R → 0 < R →
      A + ENNReal.ofReal (R ^ α) * B ≤
        ENNReal.ofReal c * (S + ENNReal.ofReal (R ^ α) * T)) :
    B ≤ ENNReal.ofReal c * T := by
  have hreal : ∀ R : ℝ, R0 ≤ R → 0 < R →
      A.toReal + R ^ α * B.toReal ≤ c * (S.toReal + R ^ α * T.toReal) := by
    intro R hR hp
    have hpower : 0 ≤ R ^ α := (Real.rpow_pos_of_pos hp α).le
    have hfin : ENNReal.ofReal c * (S + ENNReal.ofReal (R ^ α) * T) ≠ ⊤ :=
      ENNReal.mul_ne_top ENNReal.ofReal_ne_top
        (ENNReal.add_ne_top.mpr ⟨hS, ENNReal.mul_ne_top ENNReal.ofReal_ne_top hT⟩)
    have he := ENNReal.toReal_mono hfin (hscale R hR hp)
    simpa only [ENNReal.toReal_add hA (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hB),
      ENNReal.toReal_add hS (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hT),
      ENNReal.toReal_mul, ENNReal.toReal_ofReal hpower, ENNReal.toReal_ofReal hc] using he
  have hr := holder_seminorm_bound_of_scaled_full_norm_bound hα ENNReal.toReal_nonneg hreal
  apply (ENNReal.toReal_le_toReal hB (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hT)).mp
  simpa only [ENNReal.toReal_mul, ENNReal.toReal_ofReal hc] using hr

end RothschildStein.H3
