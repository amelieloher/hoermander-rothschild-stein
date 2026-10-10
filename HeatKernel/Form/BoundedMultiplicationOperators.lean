-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Form.BoundedL2Multipliers
import Mathlib.Tactic.Linter

/-! # Bounded multiplication as a continuous linear operator on L² -/

@[expose] public section

noncomputable section

open MeasureTheory

namespace HeatKernel

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {a : α → ℝ} {C : ℝ} (ha : AEStronglyMeasurable a μ) (hC : 0 ≤ C)
    (hb : ∀ᵐ x ∂μ, ‖a x‖ ≤ C)

/-- Multiplication by a bounded coefficient is real linear on L². -/
def boundedL2MulLinearMap : Lp ℝ 2 μ →ₗ[ℝ] Lp ℝ 2 μ where
  toFun := boundedL2Mul ha hC hb
  map_add' u v := by
    apply Lp.ext
    filter_upwards [boundedL2Mul_ae ha hC hb (u + v), boundedL2Mul_ae ha hC hb u,
      boundedL2Mul_ae ha hC hb v, Lp.coeFn_add u v,
      Lp.coeFn_add (boundedL2Mul ha hC hb u) (boundedL2Mul ha hC hb v)] with x h h1 h2 h3 h4
    simp only [Pi.add_apply] at h3 h4
    rw [h, h4, h1, h2, h3, mul_add]
  map_smul' c u := by
    simp only [RingHom.id_apply]
    apply Lp.ext
    filter_upwards [boundedL2Mul_ae ha hC hb (c • u), boundedL2Mul_ae ha hC hb u,
      Lp.coeFn_smul c u, Lp.coeFn_smul c (boundedL2Mul ha hC hb u)] with x h h1 h2 h3
    simp only [Pi.smul_apply, smul_eq_mul] at h2 h3
    rw [h, h3, h1, h2]
    ring

/-- Multiplication has norm bound given by the essential coefficient bound. -/
theorem norm_boundedL2Mul_le (u : Lp ℝ 2 μ) :
    ‖boundedL2Mul ha hC hb u‖ ≤ C * ‖u‖ := by
  apply Lp.norm_le_mul_norm_of_ae_le_mul
  filter_upwards [boundedL2Mul_ae ha hC hb u, hb] with x hx hb
  rw [hx, norm_mul]
  exact mul_le_mul_of_nonneg_right hb (norm_nonneg _)

/-- The bounded real multiplication operator on L². -/
def boundedL2MulContinuousLinearMap : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ :=
  (boundedL2MulLinearMap ha hC hb).mkContinuous C (norm_boundedL2Mul_le ha hC hb)

/-- Evaluation of the bounded operator is the original multiplication map. -/
@[simp] theorem boundedL2MulContinuousLinearMap_apply (u : Lp ℝ 2 μ) :
    boundedL2MulContinuousLinearMap ha hC hb u = boundedL2Mul ha hC hb u := rfl

end HeatKernel
