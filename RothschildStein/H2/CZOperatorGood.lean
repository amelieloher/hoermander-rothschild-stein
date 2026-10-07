-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H2.CZGoodEnergy
public import RothschildStein.H2.OperatorEnergy
public import RothschildStein.H2.WeakEnergy
public import RothschildStein.H2.LocDoubling

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set MeasureTheory
open scoped ENNReal BigOperators Classical

namespace RothschildStein.H2
variable {X ι : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [Countable ι]

omit [Countable ι] in
/-- The operator's good-part distribution has coefficient
4*cT²*cg/α (BB pp. 319–320). -/
theorem CZDecompositionFacts.operator_good_distribution (D : LocDoubling X)
    {U : Set X} (hU : U ⊆ D.Ω₂)
    (T : Lp ℝ 2 (D.μ.restrict U) →L[ℝ] Lp ℝ 2 (D.μ.restrict U))
    {cT C α : ℝ} (hcT : ‖T‖ ≤ cT) (hC : 0 ≤ C) (hα : 0 < α)
    {B : ι → Set X} {f g : X → ℝ} {b : ι → X → ℝ}
    (hcz : CZDecompositionFacts (D.μ.restrict D.Ω₂) B f (C * α) g b)
    (hf : IntegrableOn f D.Ω₂ D.μ) (hn : ∀ᵐ x ∂D.μ.restrict D.Ω₂, 0 ≤ f x) :
    ∃ hgU : MemLp g 2 (D.μ.restrict U),
      distribution (D.μ.restrict U) (fun x => (T (hgU.toLp g)) x) (α / 2) ≤
        ENNReal.ofReal (4 * cT ^ 2 * C / α) * ∫⁻ x in D.Ω₂, ‖f x‖ₑ ∂D.μ := by
  let : IsFiniteMeasure (D.μ.restrict D.Ω₂) := ⟨by simpa using D.finΩ₂⟩
  have hg2 : MemLp g 2 (D.μ.restrict D.Ω₂) := hcz.2.2.2.2.2.2.2.2.2.2.2.2.2 2 inferInstance
  have hmeasure := Measure.restrict_mono hU (le_rfl : D.μ ≤ D.μ)
  have hgU : MemLp g 2 (D.μ.restrict U) := hg2.mono_measure hmeasure
  have he : (∫⁻ x, ‖(hgU.toLp g) x‖ₑ ^ 2 ∂D.μ.restrict U) =
      ∫⁻ x, ‖g x‖ₑ ^ 2 ∂D.μ.restrict U :=
    lintegral_congr_ae (hgU.coeFn_toLp.fun_comp fun t => ‖t‖ₑ ^ 2)
  have hc0 : 0 ≤ cT := (norm_nonneg T).trans hcT
  have henergy : (∫⁻ x, ‖(T (hgU.toLp g)) x‖ₑ ^ 2 ∂D.μ.restrict U) ≤
      ENNReal.ofReal ((cT ^ 2 * C) * α) * ∫⁻ x in D.Ω₂, ‖f x‖ₑ ∂D.μ := by
    calc
      _ ≤ ENNReal.ofReal cT ^ 2 * ∫⁻ x, ‖(hgU.toLp g) x‖ₑ ^ 2 ∂D.μ.restrict U :=
        operator_square_integral_le (D.μ.restrict U) T hcT _
      _ = ENNReal.ofReal cT ^ 2 * ∫⁻ x, ‖g x‖ₑ ^ 2 ∂D.μ.restrict U := by rw [he]
      _ ≤ ENNReal.ofReal cT ^ 2 * ∫⁻ x in D.Ω₂, ‖g x‖ₑ ^ 2 ∂D.μ :=
        mul_le_mul' le_rfl (lintegral_mono' hmeasure le_rfl)
      _ ≤ ENNReal.ofReal cT ^ 2 *
          (ENNReal.ofReal (C * α) * ∫⁻ x in D.Ω₂, ‖f x‖ₑ ∂D.μ) :=
        mul_le_mul' le_rfl (hcz.good_square_integral (D.μ.restrict D.Ω₂) hf hn)
      _ = _ := by
        rw [← ENNReal.ofReal_pow hc0, ← mul_assoc, ← ENNReal.ofReal_mul (sq_nonneg cT)]
        congr 2
        ring
  refine ⟨hgU, ?_⟩
  simpa only [mul_assoc] using (distribution_half_le_of_square_bound (D.μ.restrict U) _
    (Lp.aestronglyMeasurable _).aemeasurable hα (mul_nonneg (sq_nonneg cT) hC) _ henergy)

end RothschildStein.H2
