-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H1.GaugeIncrement
public import RothschildStein.G2.NormConstruction
public import Mathlib.MeasureTheory.Integral.Bochner.Set

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
attribute [local irreducible] RothschildStein.HomogeneousGroup.inv RothschildStein.HomogeneousGroup.mul
open Set MeasureTheory Filter
namespace RothschildStein.H1
variable {N : ℕ} (G : HomogeneousGroup N)

/-- Step 3: transporting a compactly supported integrable
coefficient by a small group dilation gives a uniform Cε error
against a compact C¹ test. -/
theorem exists_smallDilationTransport_integral_bound
    {ν a ψ : (Fin N → ℝ) → ℝ} (hν : G.IsHomogeneousGauge ν)
    (ha : Integrable a volume) {R : ℝ} (hR : 0 < R)
    (hsa : ∀ v, R < ν v → a v = 0)
    (hc : ContDiff ℝ 1 ψ) (hs : HasCompactSupport ψ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ ε : ℝ, 0 < ε → ε ≤ 1 → ∀ x,
      ‖∫ v, a v * (ψ (G.mul x (G.inv (G.dilate ε v))) - ψ x)‖ ≤ C * ε := by
  let νN := G2.normOfGauge ν hν
  have hci : 0 < νN.c := zero_lt_one.trans_le νN.one_le_c
  obtain ⟨L, hL, hb⟩ := exists_gaugeIncrement_bound G hν hc hs (mul_pos hci hR)
  let B := L * (νN.c * R)
  have hB : 0 ≤ B := mul_nonneg hL (mul_nonneg hci.le hR.le)
  refine ⟨B * (∫ v, ‖a v‖), mul_nonneg hB (integral_nonneg fun _ => norm_nonneg _), ?_⟩
  intro ε hε hε1 x
  have hpoint (v : Fin N → ℝ) :
      ‖a v * (ψ (G.mul x (G.inv (G.dilate ε v))) - ψ x)‖ ≤ ‖a v‖ * (B * ε) := by
    by_cases hv : R < ν v
    · rw [hsa v hv, zero_mul, norm_zero]
      simp only [zero_mul, le_refl]
    · have hνv : ν v ≤ R := le_of_not_gt hv
      have hinv : ν (G.inv (G.dilate ε v)) ≤ ε * (νN.c * R) := by
        rw [G2.inv_dilate G hε, hν.2.2.2 ε hε]
        exact mul_le_mul_of_nonneg_left
          ((νN.inv_le v).trans (mul_le_mul_of_nonneg_left hνv hci.le)) hε.le
      have hiR : ν (G.inv (G.dilate ε v)) ≤ νN.c * R := hinv.trans
        ((mul_le_mul_of_nonneg_right hε1 (mul_nonneg hci.le hR.le)).trans_eq (one_mul _))
      have hψ : ‖ψ (G.mul x (G.inv (G.dilate ε v))) - ψ x‖ ≤ B * ε := by
        rw [Real.norm_eq_abs]
        calc
          _ ≤ |ψ (G.mul x (G.inv (G.dilate ε v))) - ψ x| +
              |ψ (G.mul (G.inv (G.dilate ε v)) x) - ψ x| := le_add_of_nonneg_right (abs_nonneg _)
          _ ≤ L * ν (G.inv (G.dilate ε v)) := hb x _ hiR
          _ ≤ L * (ε * (νN.c * R)) := mul_le_mul_of_nonneg_left hinv hL
          _ = _ := by dsimp [B]; ring
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_left hψ (norm_nonneg _)
  calc
    _ ≤ ∫ v, ‖a v‖ * (B * ε) :=
      norm_integral_le_of_norm_le (ha.norm.mul_const _) (Eventually.of_forall hpoint)
    _ = _ := by rw [integral_mul_const]; ring

end RothschildStein.H1
