-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module
public import RothschildStein.G3.LocalScalarTaylor

@[expose] public section
noncomputable section
open Filter
open scoped Topology
namespace RothschildStein.G3

theorem projected_curve_jets_eq_of_power_error
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f g : ℝ → E} {n : ℕ} {C : ℝ}
    (L : E →L[ℝ] ℝ)
    (hf : ContDiffAt ℝ n f 0) (hg : ContDiffAt ℝ n g 0)
    (hbound : ∀ᶠ t : ℝ in 𝓝 0, ‖f t - g t‖ ≤ C * |t| ^ (n + 1)) :
    ∀ k ≤ n, iteratedDeriv k (fun t => L (f t)) 0 =
      iteratedDeriv k (fun t => L (g t)) 0 := by
  apply scalar_jets_eq_of_power_error_at
      (L.contDiff.contDiffAt.comp 0 hf) (L.contDiff.contDiffAt.comp 0 hg)
      (C := ‖L‖ * C)
  filter_upwards [hbound] with t ht
  calc
    ‖L (f t) - L (g t)‖ = ‖L (f t - g t)‖ := by rw [map_sub]
    _ ≤ ‖L‖ * ‖f t - g t‖ := L.le_opNorm _
    _ ≤ ‖L‖ * (C * |t| ^ (n + 1)) := mul_le_mul_of_nonneg_left ht (norm_nonneg _)
    _ = (‖L‖ * C) * |t| ^ (n + 1) := by ring

end RothschildStein.G3
