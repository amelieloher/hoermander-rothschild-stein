-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module
public import RothschildStein.G3.ShortFlowRescaling
@[expose] public section
noncomputable section
namespace RothschildStein.G3

def coefficientRescalingMap {m N : ℕ} (θ : ℝ) :
    ((Fin m → ℝ) × (Fin N → ℝ)) →L[ℝ] ((Fin m → ℝ) × (Fin N → ℝ)) :=
  (θ⁻¹ • ContinuousLinearMap.fst ℝ (Fin m → ℝ) (Fin N → ℝ)).prod
    (ContinuousLinearMap.snd ℝ (Fin m → ℝ) (Fin N → ℝ))

theorem coefficientRescalingMap_apply {m N : ℕ} (θ : ℝ)
    (q : (Fin m → ℝ) × (Fin N → ℝ)) : coefficientRescalingMap θ q = (θ⁻¹ • q.1,q.2) := rfl

theorem norm_coefficientRescalingMap_le {m N : ℕ} (θ : ℝ) :
    ‖coefficientRescalingMap (m := m) (N := N) θ‖ ≤ 1+|θ⁻¹| := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro q
  rw [coefficientRescalingMap_apply,Prod.norm_def]
  apply max_le
  · rw [norm_smul,Real.norm_eq_abs]
    apply mul_le_mul (by linarith [abs_nonneg θ⁻¹]) (norm_fst_le q)
      (norm_nonneg _) (by positivity)
  · exact (norm_snd_le q).trans
      (le_mul_of_one_le_left (norm_nonneg _) (by linarith [abs_nonneg θ⁻¹]))
end RothschildStein.G3
