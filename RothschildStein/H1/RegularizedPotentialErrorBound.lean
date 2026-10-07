-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H1.HomogeneousWeightedBallBound
public import RothschildStein.H1.RegularizedPotentialDifference

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
open Set MeasureTheory
namespace RothschildStein.H1
variable {N : ℕ} (G : HomogeneousGroup N)

/-- Step 2: smooth cutoff potentials approach the original
homogeneous potential with a uniform C(Rε)^(Q+β) error. -/
theorem exists_regularizedPotential_error_bound
    {ν f η ψ : (Fin N → ℝ) → ℝ} (hν : G.IsHomogeneousGauge ν)
    (hf : ContinuousOn f {(0 : Fin N → ℝ)}ᶜ) {β : ℝ}
    (hhom : ∀ t : ℝ, 0 < t → ∀ x, x ≠ 0 → f (G.dilate t x) = t ^ β * f x)
    (hβ : -(G.homogeneousDimension : ℝ) < β)
    (hη : Continuous η) {R : ℝ} (hR : 0 < R)
    (hηout : ∀ w, R ≤ ν w → η w = 0) (hbη : ∀ w, ‖η w‖ ≤ 1)
    (hcψ : Continuous ψ) (hsψ : HasCompactSupport ψ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ ε : ℝ, 0 < ε → ∀ x,
      ‖G2.groupConvolution G ψ (fun w => f w * (1 - η (G.dilate ε⁻¹ w))) x - G2.groupConvolution G ψ f x‖ ≤
        C * (R * ε) ^ ((G.homogeneousDimension : ℝ) + β) := by
  obtain ⟨B, hB⟩ := hsψ.exists_bound_of_continuous hcψ
  let M := max B 0
  have hM : 0 ≤ M := le_max_right _ _
  have hψ (v : Fin N → ℝ) : ‖ψ v‖ ≤ M := (hB v).trans (le_max_left _ _)
  obtain ⟨C, hC, hb⟩ := exists_homogeneousKernel_weightedBall_bound G hν hf hhom hβ hM
  have hi := locallyIntegrable_homogeneousKernel G hν hf hhom hβ
  refine ⟨C, hC, ?_⟩
  intro ε hε x
  rw [regularizedPotential_sub_eq_neg_weightedSmallBall G hν hi hη hε hηout hcψ hsψ x, norm_neg]
  apply hb (R * ε) (mul_pos hR hε)
  intro w
  rw [norm_mul]
  exact (mul_le_mul (hbη _) (hψ _) (norm_nonneg _) zero_le_one).trans_eq (one_mul _)

end RothschildStein.H1
