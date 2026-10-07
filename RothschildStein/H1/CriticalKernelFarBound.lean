-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H1.HomogeneousKernelBound

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
open Set
namespace RothschildStein.H1
variable {N : ℕ} (G : HomogeneousGroup N)

/-- A critical homogeneous kernel is uniformly bounded
outside the unit gauge ball (BB Proposition 6.29, pp. 276–278). -/
theorem exists_criticalKernel_far_bound
    {ν F : (Fin N → ℝ) → ℝ} (hν : G.IsHomogeneousGauge ν)
    (hF : ContinuousOn F {(0 : Fin N → ℝ)}ᶜ)
    (hhom : ∀ t : ℝ, 0 < t → ∀ x, x ≠ 0 →
      F (G.dilate t x) = t ^ (-(G.homogeneousDimension : ℝ)) * F x) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ w, 1 ≤ ν w → ‖F w‖ ≤ C := by
  obtain ⟨C, hC, hb⟩ := exists_homogeneousKernel_gauge_bound G hν hF hhom
  refine ⟨C, hC, ?_⟩
  intro w hw
  have hw0 : w ≠ 0 := by
    intro he
    rw [he, (hν.2.2.1 0).mpr rfl] at hw
    norm_num at hw
  have hp : (ν w) ^ (-(G.homogeneousDimension : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos hw (neg_nonpos.mpr (Nat.cast_nonneg _))
  exact (hb w hw0).trans ((mul_le_mul_of_nonneg_left hp hC).trans_eq (mul_one _))

end RothschildStein.H1
