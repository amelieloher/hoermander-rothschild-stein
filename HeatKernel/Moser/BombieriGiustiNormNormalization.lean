-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Moser.BombieriGiustiMeasureNormalization

/-! # Cancellation of reference-measure powers in reverse Hölder norms -/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open scoped ENNReal
namespace HeatKernel

/-- Normalizing both moment norms cancels the reference factor in the reverse
Hölder geometric constant, with its exact exponent difference retained. -/
theorem reverseHolder_norm_bound_mul_normalization {R F m n : ℝ≥0∞}
    (hRzero : R ≠ 0) (hRfinite : R ≠ ⊤) {p p₀ : ℝ}
    (hp : 0 < p) (hp₀ : 0 < p₀) (hpp₀ : p ≤ p₀)
    (hbound : m ^ (1 / p₀) ≤ (F * R) ^ (1 / p - 1 / p₀) * n ^ (1 / p)) :
    (R * m) ^ (1 / p₀) ≤ F ^ (1 / p - 1 / p₀) * (R * n) ^ (1 / p) := by
  have hdiff : 0 ≤ 1 / p - 1 / p₀ :=
    sub_nonneg.mpr (one_div_le_one_div_of_le hp hpp₀)
  have hR : R ^ (1 / p₀) * R ^ (1 / p - 1 / p₀) = R ^ (1 / p) := by
    rw [← ENNReal.rpow_add _ _ hRzero hRfinite]
    congr 1
    ring
  calc
    (R * m) ^ (1 / p₀) = R ^ (1 / p₀) * m ^ (1 / p₀) :=
      ENNReal.mul_rpow_of_nonneg _ _ (one_div_nonneg.mpr hp₀.le)
    _ ≤ R ^ (1 / p₀) * ((F * R) ^ (1 / p - 1 / p₀) * n ^ (1 / p)) :=
      mul_le_mul' le_rfl hbound
    _ = F ^ (1 / p - 1 / p₀) * (R * n) ^ (1 / p) := by
      rw [ENNReal.mul_rpow_of_nonneg F R hdiff,
        ENNReal.mul_rpow_of_nonneg R n (one_div_nonneg.mpr hp.le)]
      calc
        _ = F ^ (1 / p - 1 / p₀) *
            ((R ^ (1 / p₀) * R ^ (1 / p - 1 / p₀)) * n ^ (1 / p)) := by ac_rfl
        _ = _ := by rw [hR]

end HeatKernel
