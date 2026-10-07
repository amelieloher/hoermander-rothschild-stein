-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.S.HolderBounds
public import Mathlib.Topology.MetricSpace.UniformConvergence

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
open Set Filter
open scoped ENNReal Topology
namespace RothschildStein.S
variable {n : ℕ} {ι : Type*}

/-- Convergence in the Hölder norm implies uniform
convergence on its domain (BB Prop 2.15, p. 82; sup-norm component). -/
theorem tendstoUniformlyOn_of_holderENorm_error_tendsto
    (d : (Fin n → ℝ) → (Fin n → ℝ) → ℝ≥0∞) (α : ℝ)
    (V : Set (Fin n → ℝ)) (F : ι → (Fin n → ℝ) → ℝ)
    (f : (Fin n → ℝ) → ℝ) {l : Filter ι}
    (ht : Tendsto (fun j => holderENorm d α V (fun x => F j x-f x)) l (𝓝 0)) :
    TendstoUniformlyOn F f l V := by
  apply Metric.tendstoUniformlyOn_iff.mpr
  intro ε he
  have hh : (0 : ℝ≥0∞) < ENNReal.ofReal (ε/2) := ENNReal.ofReal_pos.mpr (half_pos he)
  filter_upwards [ENNReal.tendsto_nhds_zero.mp ht _ hh] with j hj
  intro x hx
  have H := (enorm_le_holderENorm d α V (fun y => F j y-f y) hx).trans hj
  have hr : |F j x-f x| ≤ ε/2 :=
    (ENNReal.ofReal_le_ofReal_iff (half_pos he).le).mp H
  simpa only [Real.dist_eq,abs_sub_comm] using hr.trans_lt (half_lt_self he)

end RothschildStein.S
