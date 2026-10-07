-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H1.ShellScaling
public import RothschildStein.G2.HomogeneousType

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public section
noncomputable section
open Set MeasureTheory
namespace RothschildStein.H1
variable {N : ℕ} (G : HomogeneousGroup N)

/-- Step 4: the exact weighted gauge-ball scaling law for
a punctured homogeneous kernel; no integrability is inferred by this
algebraic identity alone. -/
theorem integral_homogeneousBall_weighted_dilate
    {ν f θ : (Fin N → ℝ) → ℝ} (hν : G.IsHomogeneousGauge ν) {β R : ℝ}
    (hf : ∀ t : ℝ, 0 < t → ∀ x, x ≠ 0 → f (G.dilate t x) = t ^ β * f x)
    {ε : ℝ} (hε : 0 < ε) :
    (∫ w in {w | ν w ≤ R * ε}, f w * θ (G.dilate ε⁻¹ w)) =
      ε ^ (β + (G.homogeneousDimension : ℝ)) * ∫ v in {v | ν v ≤ R}, f v * θ v := by
  have : Nonempty (Fin N) := ⟨⟨0, G.dimension_pos⟩⟩
  let a := {w | ν w ≤ R * ε}.indicator (fun w => f w * θ (G.dilate ε⁻¹ w))
  have he : (fun v => a (G.dilate ε v)) =ᵐ[volume]
      fun v => ε ^ β * {v | ν v ≤ R}.indicator (fun v => f v * θ v) v := by
    filter_upwards [volume.ae_ne (0 : Fin N → ℝ)] with v hv
    have hm : (ν (G.dilate ε v) ≤ R * ε) ↔ ν v ≤ R := by
      rw [hν.2.2.2 ε hε]
      constructor <;> intro h <;> nlinarith
    dsimp only [a]
    simp only [indicator_apply, mem_ofPred_eq, hm, G2.dilate_inv_dilate G hε.ne']
    split_ifs
    · rw [hf ε hε v hv]
      ring
    · rw [mul_zero]
  have hs : (∫ v, a v) = ε ^ G.homogeneousDimension * ∫ v, a (G.dilate ε v) := by
    rw [G2.integral_dilate G hε]
    simp only [smul_eq_mul]
    rw [← mul_assoc, mul_inv_cancel₀ (ne_of_gt (pow_pos hε _)), one_mul]
  have hmR : MeasurableSet {v | ν v ≤ R} := (isClosed_le hν.1 continuous_const).measurableSet
  have hmε : MeasurableSet {v | ν v ≤ R * ε} := (isClosed_le hν.1 continuous_const).measurableSet
  rw [← integral_indicator hmε]
  change (∫ v, a v) = _
  rw [hs, integral_congr_ae he, integral_const_mul, integral_indicator hmR,
    ← mul_assoc, ← Real.rpow_natCast, ← Real.rpow_add hε]
  congr 2
  ring

end RothschildStein.H1
