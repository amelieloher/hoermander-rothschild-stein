-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H3.RadialCutoffGeometry
public import RothschildStein.H3.Truncation

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public section
noncomputable section
open Set
namespace RothschildStein.H3

/-- The nonsingular radial remainder, with an outer plateau
through radius two and support through radius three. -/
def typeZeroRemainderCutoff {N : ℕ} (ν : (Fin N → ℝ) → ℝ) (z : Fin N → ℝ) : ℝ :=
  radialKernelCutoffProfile 1 (ν z) * (1 - radialCutoff (ν z))

/-- Exact range, continuity, outer support, inner gap, and the
control Lipschitz bound of the actual remainder cutoff. -/
theorem typeZeroRemainderCutoff_properties {N : ℕ} (G : HomogeneousGroup N)
    (ν : G2.HomogeneousNorm G) (h1 : ν.c = 1) (hsym : ν.Symmetric) :
    (∀ z, 0 ≤ typeZeroRemainderCutoff ν z ∧ typeZeroRemainderCutoff ν z ≤ 1) ∧
    Continuous (typeZeroRemainderCutoff ν) ∧
    (∀ z, (3 : ℝ) ≤ ν z → typeZeroRemainderCutoff ν z = 0) ∧
    (∀ z, ν z ≤ 1 → typeZeroRemainderCutoff ν z = 0) ∧
    (∀ a b, |typeZeroRemainderCutoff ν a - typeZeroRemainderCutoff ν b| ≤
      2 * G2.gaugeDistance G ν a b) := by
  have ho := radialKernelCutoff_properties ν h1 hsym (show (0 : ℝ) < 1 by norm_num)
  dsimp only at ho
  have hi (z : Fin N → ℝ) : 0 ≤ 1 - radialCutoff (ν z) ∧ 1 - radialCutoff (ν z) ≤ 1 := by
    have h := radialCutoff_bounds (ν z)
    constructor <;> linarith
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro z
    refine ⟨mul_nonneg (ho.1 z).1 (hi z).1, ?_⟩
    exact (mul_le_mul_of_nonneg_right (ho.1 z).2 (hi z).1).trans (by simpa using (hi z).2)
  · exact ho.2.2.2.1.mul (continuous_const.sub (radialCutoff_lipschitz.continuous.comp ν.gauge.1))
  · intro z hz
    unfold typeZeroRemainderCutoff
    rw [ho.2.2.1 z (by simpa using hz), zero_mul]
  · intro z hz
    unfold typeZeroRemainderCutoff
    rw [radialCutoff_eq_one hz, sub_self, mul_zero]
  · intro a b
    have hrad := radialCutoff_lipschitz.dist_le_mul (ν a) (ν b)
    simp only [Real.dist_eq, NNReal.coe_one, one_mul] at hrad
    have hr : |radialCutoff (ν a) - radialCutoff (ν b)| ≤ G2.gaugeDistance G ν a b :=
      hrad.trans (homogeneousNorm_sub_le_gaugeDistance ν h1 hsym a b)
    have hout : |radialKernelCutoffProfile 1 (ν a) - radialKernelCutoffProfile 1 (ν b)| ≤
        G2.gaugeDistance G ν a b := by simpa only [div_one] using ho.2.2.2.2.2 a b
    have hin : |(1 - radialCutoff (ν a)) - (1 - radialCutoff (ν b))| ≤
        G2.gaugeDistance G ν a b := by
      rw [show (1 - radialCutoff (ν a)) - (1 - radialCutoff (ν b)) =
        -(radialCutoff (ν a) - radialCutoff (ν b)) by ring, abs_neg]
      exact hr
    have he : typeZeroRemainderCutoff ν a - typeZeroRemainderCutoff ν b =
        radialKernelCutoffProfile 1 (ν a) * ((1 - radialCutoff (ν a)) - (1 - radialCutoff (ν b))) +
        (radialKernelCutoffProfile 1 (ν a) - radialKernelCutoffProfile 1 (ν b)) *
          (1 - radialCutoff (ν b)) := by unfold typeZeroRemainderCutoff; ring
    rw [he]
    calc
      _ ≤ |radialKernelCutoffProfile 1 (ν a)| *
          |(1 - radialCutoff (ν a)) - (1 - radialCutoff (ν b))| +
          |radialKernelCutoffProfile 1 (ν a) - radialKernelCutoffProfile 1 (ν b)| *
          |1 - radialCutoff (ν b)| := by
        rw [← abs_mul, ← abs_mul]
        exact abs_add_le _ _
      _ ≤ 1 * G2.gaugeDistance G ν a b + G2.gaugeDistance G ν a b * 1 :=
        add_le_add (mul_le_mul (by simpa only [abs_of_nonneg (ho.1 a).1] using (ho.1 a).2)
          hin (abs_nonneg _) zero_le_one)
          (mul_le_mul hout (by simpa only [abs_of_nonneg (hi b).1] using (hi b).2)
            (abs_nonneg _) (ν.gauge.2.1 _))
      _ = _ := by ring

end RothschildStein.H3
