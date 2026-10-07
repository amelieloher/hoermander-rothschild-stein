-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module
public import RothschildStein.G3.ProjectedCurveJets

@[expose] public section
noncomputable section
open Filter
open scoped Topology
namespace RothschildStein.G3

theorem radial_projected_jets_eq_of_power_error
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f g : E → F} {n : ℕ} {C : ℝ}
    (L : F →L[ℝ] ℝ) (v : E)
    (hf : ContDiffAt ℝ n f 0) (hg : ContDiffAt ℝ n g 0)
    (hbound : ∀ᶠ x : E in 𝓝 0, ‖f x - g x‖ ≤ C * ‖x‖ ^ (n + 1)) :
    ∀ k ≤ n, iteratedDeriv k (fun t : ℝ => L (f (t • v))) 0 =
      iteratedDeriv k (fun t : ℝ => L (g (t • v))) 0 := by
  have hc : ContDiffAt ℝ n (fun t : ℝ => t • v) 0 :=
    contDiffAt_id.smul contDiffAt_const
  have hfc : ContDiffAt ℝ n (fun t : ℝ => f (t • v)) 0 := by
    simpa only [Function.comp_def, zero_smul] using (show ContDiffAt ℝ n f ((0 : ℝ) • v) by simpa using hf).comp 0 hc
  have hgc : ContDiffAt ℝ n (fun t : ℝ => g (t • v)) 0 := by
    simpa only [Function.comp_def, zero_smul] using (show ContDiffAt ℝ n g ((0 : ℝ) • v) by simpa using hg).comp 0 hc
  apply projected_curve_jets_eq_of_power_error L hfc hgc (C := C * ‖v‖ ^ (n + 1))
  have ht : Tendsto (fun t : ℝ => t • v) (𝓝 0) (𝓝 0) := by
    simpa only [zero_smul] using (show Tendsto (fun t : ℝ => t • v) (𝓝 0) (𝓝 ((0 : ℝ) • v)) from hc.continuousAt)
  filter_upwards [ht.eventually hbound] with t h
  calc
    ‖f (t • v) - g (t • v)‖ ≤ C * ‖t • v‖ ^ (n + 1) := h
    _ = (C * ‖v‖ ^ (n + 1)) * |t| ^ (n + 1) := by
      rw [norm_smul, Real.norm_eq_abs, mul_pow]
      ring

end RothschildStein.G3
