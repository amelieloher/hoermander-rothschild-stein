-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H1.GaugeIncrement
public import RothschildStein.H1.HomogeneousKernelBound
public import RothschildStein.G2.NormConstruction

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public section
noncomputable section
open Set
namespace RothschildStein.H1
variable {N : ℕ} (G : HomogeneousGroup N)

/-- The subtracted critical kernel is bounded uniformly
in the base point by ν(w)^(1−Q), including for a nonsymmetric gauge
(BB Proposition 6.29, pp. 276–278). -/
theorem exists_principalValue_near_bound
    {ν F ψ : (Fin N → ℝ) → ℝ} (hν : G.IsHomogeneousGauge ν)
    (hF : ContinuousOn F {(0 : Fin N → ℝ)}ᶜ)
    (hhom : ∀ t : ℝ, 0 < t → ∀ x, x ≠ 0 →
      F (G.dilate t x) = t ^ (-(G.homogeneousDimension : ℝ)) * F x)
    (hc : ContDiff ℝ 1 ψ) (hs : HasCompactSupport ψ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x w, ν w ≤ 1 →
      ‖F w * (ψ (G.mul x (G.inv w)) - ψ x)‖ ≤ C * (ν w) ^ (1 - (G.homogeneousDimension : ℝ)) := by
  let νN := G2.normOfGauge ν hν
  have hci : 0 < νN.c := zero_lt_one.trans_le νN.one_le_c
  obtain ⟨CF, hCF, hFb⟩ := exists_homogeneousKernel_gauge_bound G hν hF hhom
  obtain ⟨CL, hCL, hLb⟩ := exists_gaugeIncrement_bound G hν hc hs hci
  refine ⟨CF * (CL * νN.c), mul_nonneg hCF (mul_nonneg hCL hci.le), ?_⟩
  intro x w hw1
  by_cases hw : w = 0
  · subst w
    rw [G2.inv_zero, G2.mul_zero, sub_self, mul_zero, norm_zero]
    exact mul_nonneg (mul_nonneg hCF (mul_nonneg hCL hci.le))
      (Real.rpow_nonneg (hν.2.1 0) _)
  ·
    have hi : ν (G.inv w) ≤ νN.c * ν w := νN.inv_le w
    have hi1 : ν (G.inv w) ≤ νN.c := hi.trans
      ((mul_le_mul_of_nonneg_left hw1 hci.le).trans_eq (mul_one _))
    have hl : ‖ψ (G.mul x (G.inv w)) - ψ x‖ ≤ (CL * νN.c) * ν w := by
      rw [Real.norm_eq_abs]
      have hsum := hLb x (G.inv w) hi1
      calc
        _ ≤ |ψ (G.mul x (G.inv w)) - ψ x| + |ψ (G.mul (G.inv w) x) - ψ x| :=
          le_add_of_nonneg_right (abs_nonneg _)
        _ ≤ CL * ν (G.inv w) := hsum
        _ ≤ CL * (νN.c * ν w) := mul_le_mul_of_nonneg_left hi hCL
        _ = (CL * νN.c) * ν w := by ring
    have hp : 0 < ν w := G2.gauge_pos hν hw
    have he : (ν w) ^ (-(G.homogeneousDimension : ℝ)) * ν w =
        (ν w) ^ (1 - (G.homogeneousDimension : ℝ)) := by
      calc
        _ = (ν w) ^ (-(G.homogeneousDimension : ℝ)) * (ν w) ^ (1 : ℝ) := by rw [Real.rpow_one]
        _ = (ν w) ^ (-(G.homogeneousDimension : ℝ) + 1) := (Real.rpow_add hp _ _).symm
        _ = _ := by congr 1; ring
    rw [norm_mul]
    calc
      _ ≤ (CF * (ν w) ^ (-(G.homogeneousDimension : ℝ))) * ((CL * νN.c) * ν w) :=
        mul_le_mul (hFb w hw) hl (norm_nonneg _)
          (mul_nonneg hCF (Real.rpow_nonneg hp.le _))
      _ = (CF * (CL * νN.c)) * ((ν w) ^ (-(G.homogeneousDimension : ℝ)) * ν w) := by ring
      _ = _ := by rw [he]

end RothschildStein.H1
