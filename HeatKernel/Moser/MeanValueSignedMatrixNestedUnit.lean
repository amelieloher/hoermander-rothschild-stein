-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Moser.MeanValueSignedMatrixNestedCylinders
public import HeatKernel.Moser.MeanValueNormalizedScaling
public import HeatKernel.Moser.MeanValueSignedMatrixNestedPowers
import Mathlib.Tactic

/-! # Normalized unit mean values with arbitrary interior ratios -/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set MeasureTheory TopologicalSpace RothschildStein
open scoped ENNReal
namespace HeatKernel
set_option backward.isDefEq.respectTransparency false

/-- Each fixed positive aspect ratio and strictly smaller inner time and radius
factors give a normalized mean-value estimate on the unit spatial ball for every
fixed positive power. The constant is chosen before the signed
uniformly elliptic matrix weak solution. -/
theorem exists_uniform_signed_matrix_nested_unit_positive_power_mean_value {N q : ℕ}
    (G : HomogeneousGroup N) (hq : q ≤ N) (hqpos : 0 < q)
    (hspan : bracketSpansOn univ (G.horizontalFields hq))
    (hw : ∀ i : Fin q, G.weight (Fin.castLE hq i) = 1)
    {p τ θ ρ : ℝ} (hp : 0 < p) (hτ : 0 < τ) (hθτ : θ < τ) (hρone : ρ < 1)
    (ell upper : ℝ) (hell : 0 < ell) (hupper : 0 ≤ upper) :
    ∃ C : ℝ, 0 < C ∧ ∀ (v : ℝ × (Fin N → ℝ) → ℝ)
      (coeff : ℝ → (Fin N → ℝ) → Fin q → Fin q → ℝ),
      IsLocalWeakSolution G hq hqpos hw hspan
        coeff
        ⟨Ioo (-τ) 0, isOpen_Ioo⟩
        ⟨horizontalBall (G.horizontalFields hq) 0 1,
          isOpen_horizontalBall G hq hqpos hspan 0 1⟩ (fun t x => v (t, x)) →
      (∀ i j, Measurable (fun z : ℝ × (Fin N → ℝ) => coeff z.1 z.2 i j)) →
      (∀ᵐ z : ℝ × (Fin N → ℝ) ∂volume,
        (∀ i j, coeff z.1 z.2 i j = coeff z.1 z.2 j i) ∧ ∀ ξ : Fin q → ℝ,
          ell * ∑ i, ξ i ^ 2 ≤ ∑ i, ∑ j, coeff z.1 z.2 i j * ξ i * ξ j ∧
          ∑ i, ∑ j, coeff z.1 z.2 i j * ξ i * ξ j ≤ upper * ∑ i, ξ i ^ 2) →
      eLpNormEssSup v (volume.restrict
        (Ioo (-θ) 0 ×ˢ horizontalBall (G.horizontalFields hq) 0 ρ)) ≤
        ENNReal.ofReal C * eLpNorm v (ENNReal.ofReal p)
          (((volume : Measure (ℝ × (Fin N → ℝ)))
            (Ioo (-τ) 0 ×ˢ horizontalBall (G.horizontalFields hq) 0 1))⁻¹ •
              volume.restrict (Ioo (-τ) 0 ×ˢ horizontalBall (G.horizontalFields hq) 0 1)) := by
  obtain ⟨r, hr, hrspace, hrtime⟩ := exists_positive_radius_for_cylinder_gaps
    hρone (show -τ < -θ by linarith)
  obtain ⟨C, hC, hmean⟩ := exists_uniform_signed_matrix_nested_cylinder_positive_power_bound
    G hq hqpos hspan hw hp ell upper hell hupper
  let S := Ioo (-τ) 0 ×ˢ horizontalBall (G.horizontalFields hq) 0 1
  let m := (volume : Measure (ℝ × (Fin N → ℝ))) S
  have hmass : m = ENNReal.ofReal τ * (volume : Measure (Fin N → ℝ))
      (horizontalBall (G.horizontalFields hq) 0 1) := by
    dsimp only [m, S]
    rw [Measure.volume_eq_prod, Measure.prod_prod, Real.volume_Ioo]
    simp only [sub_neg_eq_add, zero_add]
  have hm : m ≠ 0 := by
    rw [hmass]
    exact mul_ne_zero (ENNReal.ofReal_pos.mpr hτ).ne'
      (volume_horizontalBall_pos G hq hqpos hspan 0 (by norm_num)).ne'
  have hmtop : m ≠ ⊤ := by
    rw [hmass]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top
      (volume_horizontalBall_lt_top G hq hqpos hspan hw 0 (by norm_num)).ne
  let D := C * ((r ^ (G.homogeneousDimension + 2))⁻¹) ^ (1 / p)
  have hJ : 0 < (r ^ (G.homogeneousDimension + 2))⁻¹ := inv_pos.mpr (pow_pos hr _)
  have hD : 0 < D := mul_pos hC (Real.rpow_pos_of_pos hJ _)
  refine ⟨D * m.toReal ^ (1 / p),
    mul_pos hD (Real.rpow_pos_of_pos (ENNReal.toReal_pos hm hmtop) _), ?_⟩
  intro v coeff hweak ha hbound
  have hb := hmean (-τ) (-θ) 0 0 ρ 1 r hr hrspace hrtime v coeff hweak ha hbound
  rw [ENNReal.ofReal_rpow_of_pos hJ, ← mul_assoc, ← ENNReal.ofReal_mul hC.le] at hb
  change eLpNormEssSup v (volume.restrict
      (Ioo (-θ) 0 ×ˢ horizontalBall (G.horizontalFields hq) 0 ρ)) ≤
    ENNReal.ofReal D * eLpNorm v (ENNReal.ofReal p) (volume.restrict S) at hb
  rw [mul_eLpNorm_eq_normalized_eLpNorm (m := m) (volume.restrict S) v hp hD.le hm hmtop] at hb
  exact hb

end HeatKernel
