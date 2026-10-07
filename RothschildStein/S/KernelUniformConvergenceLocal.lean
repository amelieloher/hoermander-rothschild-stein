-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.S.KernelUniformConvergence
public import RothschildStein.S.KernelIncrementLocalEstimate
public import Mathlib.Topology.UniformSpace.HeineCantor
public import Mathlib.Topology.MetricSpace.Pseudo.Defs

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public section
noncomputable section
open Set MeasureTheory Function Metric Filter
open scoped Topology
namespace RothschildStein.S
variable {n : ℕ} {U : Set (Fin n → ℝ)} {δ : ℝ}

/-- Uniform continuity on the interior tube suffices for a
bounded zero-mean kernel family to converge uniformly to zero on its patch (BB Lemma 2.21, p. 87;
local data require no global continuity extension). -/
theorem tendstoUniformlyOn_friedrichsKernelOp_zero_of_uniformContinuousOn
    (K : BoundedFriedrichsKernel U δ) (hδ : 0 < δ)
    (hK : HasVanishingKernelMean K) {h : (Fin n → ℝ) → ℝ} {L : Set (Fin n → ℝ)} (hh : UniformContinuousOn h L)
    (hUL : U ⊆ L)
    (hL : ∀ ε ∈ Ioo 0 δ, ∀ x ∈ U, ∀ y ∈ closedBall (0 : Fin n → ℝ) 1,
      x+ε • y ∈ L) :
    TendstoUniformlyOn (fun ε : ℝ => friedrichsKernelOp K.toFun h ε)
      (fun _ => 0) (𝓝[>] 0) U := by
  obtain ⟨C,hC,hb⟩ := K.exists_uniform_size
  let A := C * (volume (closedBall (0 : Fin n → ℝ) 1)).toReal
  have hA : 0 ≤ A := mul_nonneg hC ENNReal.toReal_nonneg
  apply Metric.tendstoUniformlyOn_iff.mpr
  intro η hη
  let D := η / (2*(A+1))
  have hD : 0 < D := div_pos hη (by positivity)
  obtain ⟨ρ,hρ,hd⟩ := Metric.uniformContinuousOn_iff.mp hh D hD
  filter_upwards [Ioo_mem_nhdsGT (lt_min hδ hρ)] with ε hε x hx
  have hek : ε ∈ Ioo 0 δ := ⟨hε.1,hε.2.trans_le (min_le_left _ _)⟩
  have hi : ∀ y ∈ closedBall (0 : Fin n → ℝ) 1, ‖h (x+ε • y)-h x‖ ≤ D := by
    intro y hy
    have he : dist (x+ε • y) x < ρ := by
      rw [dist_eq_norm,add_sub_cancel_left,norm_smul,Real.norm_of_nonneg hε.1.le]
      have hy' : ‖y‖ ≤ 1 := by simpa only [mem_closedBall,dist_zero_right] using hy
      exact (mul_le_of_le_one_right hε.1.le hy').trans_lt (hε.2.trans_le (min_le_right _ _))
    simpa only [dist_eq_norm] using (hd (x+ε • y) (hL ε hek x hx y hy) x (hUL hx) he).le
  have H := norm_friedrichsKernelOp_le_increment_of_continuousOn K hK hh.continuousOn hek hx
    (hL ε hek x hx) C D hC (hb ε hek x hx) hi
  have hAD : A*D < η := by
    dsimp [D]
    rw [← mul_div_assoc,div_lt_iff₀ (by positivity)]
    nlinarith [mul_nonneg hA hη.le]
  simpa only [dist_zero_left,Real.norm_eq_abs] using H.trans_lt hAD

/-- Continuous data on a compact interior tube satisfy the
uniform zero-mean kernel approximation (BB Lemma 2.21, p. 87). -/
theorem tendstoUniformlyOn_friedrichsKernelOp_zero_of_compact
    (K : BoundedFriedrichsKernel U δ) (hδ : 0 < δ)
    (hK : HasVanishingKernelMean K) {L : Set (Fin n → ℝ)} (hc : IsCompact L)
    {h : (Fin n → ℝ) → ℝ} (hh : ContinuousOn h L) (hUL : U ⊆ L)
    (hL : ∀ ε ∈ Ioo 0 δ, ∀ x ∈ U, ∀ y ∈ closedBall (0 : Fin n → ℝ) 1,
      x+ε • y ∈ L) :
    TendstoUniformlyOn (fun ε : ℝ => friedrichsKernelOp K.toFun h ε)
      (fun _ => 0) (𝓝[>] 0) U :=
  tendstoUniformlyOn_friedrichsKernelOp_zero_of_uniformContinuousOn K hδ hK
    (hc.uniformContinuousOn_of_continuous hh) hUL hL

end RothschildStein.S
