-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H3.InterpolationScale

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public section
noncomputable section
namespace RothschildStein.H3
open MeasureTheory
open scoped ENNReal

/-- For smooth input, the positive-step estimate follows from the global
 group integral-curve identity. It uses spatial averaging, Taylor's
 identity, and step rescaling. -/
theorem field_step_interpolation_of_group_integralCurve {n : ℕ}
    (G : HomogeneousGroup n) (E : ℝ → (Fin n → ℝ))
    (hE : Continuous E) (hE0 : E 0 = 0)
    (V : (Fin n → ℝ) → (Fin n → ℝ)) (hV : ContDiff ℝ (⊤ : ℕ∞) V)
    (hflow : ∀ x, IsIntegralCurve (fun t => G.mul x (E t)) (fun _ => V))
    {p : ℝ≥0∞} (hp : 1 ≤ p) (hpt : p ≠ ∞)
    {u : (Fin n → ℝ) → ℝ} (hu : ContDiff ℝ (⊤ : ℕ∞) u)
    (hup : MemLp u p volume)
    (hddp : MemLp (fieldDerivative V (fieldDerivative V u)) p volume)
    {ε : ℝ} (hε : 0 < ε) :
    MemLp (fieldDerivative V u) p volume ∧
      eLpNorm (fieldDerivative V u) p volume ≤
        ENNReal.ofReal (2/ε) * eLpNorm u p volume +
        ENNReal.ofReal (ε/2) *
          eLpNorm (fieldDerivative V (fieldDerivative V u)) p volume := by
  have hEε : Continuous (fun t => E (ε*t)) := hE.comp (continuous_const.mul continuous_id)
  have hzero : E (ε*0) = 0 := by simpa only [mul_zero] using hE0
  have hflowε : ∀ x, IsIntegralCurve (fun t => G.mul x (E (ε*t)))
      (fun _ => ε • V) := fun x => integralCurve_rescale_time ε V _ (hflow x)
  have hddε : MemLp (fieldDerivative (ε • V) (fieldDerivative (ε • V) u)) p volume := by
    rw [fieldDerivative_rescale_square]
    exact hddp.const_smul (ε*ε)
  obtain ⟨hm,hb⟩ := field_unit_interpolation_of_group_integralCurve G
    (fun t => E (ε*t)) hEε hzero (ε • V) (hV.const_smul ε) hflowε hp hpt hu hup hddε
  rw [fieldDerivative_rescale] at hm
  have hmem : MemLp (fieldDerivative V u) p volume := by
    have hi := hm.const_smul ε⁻¹
    simpa only [smul_smul,inv_mul_cancel₀ hε.ne',one_smul] using hi
  refine ⟨hmem,interpolation_cancel_step hε _ _ _ ?_⟩
  rw [fieldDerivative_rescale_square,fieldDerivative_rescale,
    eLpNorm_const_smul,eLpNorm_const_smul] at hb
  have hc : ‖ε‖ₑ = ENNReal.ofReal ε := by
    rw [Real.enorm_eq_ofReal_abs,abs_of_pos hε]
  have hc2 : ‖ε*ε‖ₑ = ENNReal.ofReal ε * ENNReal.ofReal ε := by
    rw [Real.enorm_eq_ofReal_abs,abs_of_pos (mul_pos hε hε),ENNReal.ofReal_mul hε.le]
  simpa only [hc,hc2] using hb

end RothschildStein.H3
