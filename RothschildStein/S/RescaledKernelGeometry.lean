-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.S.KernelRescaling
public import RothschildStein.S.SmoothFriedrichsKernels
public import RothschildStein.S.CompactKernelLocalData

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public section
noncomputable section
open Set MeasureTheory Function Metric TopologicalSpace
open scoped Topology ContDiff
namespace RothschildStein.S
variable {n : ℕ}

/-- The integration-variable kernel is jointly smooth for each
positive scale (BB (2.11), p. 78). -/
theorem contDiff_friedrichsRescaledKernel (K : SmoothFriedrichsKernel n) (ε : ℝ) :
    ContDiff ℝ (⊤ : ℕ∞) (uncurry (friedrichsRescaledKernel K.family ε)) := by
  exact contDiff_const.mul (K.smooth.comp
    ((contDiff_fst.prodMk ((contDiff_snd.sub contDiff_fst).const_smul ε⁻¹)).prodMk
      contDiff_const))

/-- The rescaled section vanishes outside the closed ε-ball
about its base point (BB pp. 76–78). -/
theorem friedrichsRescaledKernel_eq_zero_of_dist
    (K : SmoothFriedrichsKernel n) {ε : ℝ} (hε : 0 < ε)
    (x z : Fin n → ℝ) (hz : ε < dist z x) :
    friedrichsRescaledKernel K.family ε x z = 0 := by
  have hy : 1 < ‖ε⁻¹ • (z-x)‖ := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hε)]
    rw [dist_eq_norm] at hz
    exact (lt_inv_mul_iff₀ hε).mpr (by simpa using hz)
  unfold friedrichsRescaledKernel SmoothFriedrichsKernel.family
  rw [K.vanish ((x,ε⁻¹ • (z-x)),ε) hy,mul_zero]

/-- Rescaled kernel test sections have compact support in the
closed ε-ball (BB (2.11), p. 78). -/
theorem tsupport_friedrichsRescaledKernel_subset
    (K : SmoothFriedrichsKernel n) {ε : ℝ} (hε : 0 < ε) (x : Fin n → ℝ) :
    tsupport (friedrichsRescaledKernel K.family ε x) ⊆ closedBall x ε := by
  apply closure_minimal _ isClosed_closedBall
  intro z hz
  change dist z x ≤ ε
  by_contra hn
  exact hz (friedrichsRescaledKernel_eq_zero_of_dist K hε x z (lt_of_not_ge hn))

/-- Nearby base points share one compact integration support,
allowing differentiation under the integral (BB p. 78; support). -/
theorem friedrichsRescaledKernel_eq_zero_of_notMem_common_ball
    (K : SmoothFriedrichsKernel n) {ε r : ℝ} (hε : 0 < ε)
    (x a z : Fin n → ℝ) (ha : a ∈ ball x r) (hz : z ∉ closedBall x (ε+r)) :
    friedrichsRescaledKernel K.family ε a z = 0 := by
  apply friedrichsRescaledKernel_eq_zero_of_dist K hε
  have hz' : ε+r < dist z x := lt_of_not_ge hz
  have ha' : dist a x < r := ha
  have ht := dist_triangle z a x
  linarith

end RothschildStein.S
