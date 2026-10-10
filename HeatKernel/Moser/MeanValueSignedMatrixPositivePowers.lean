-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Moser.MeanValueSignedMatrixUnitPositivePowers
public import HeatKernel.Moser.MeanValueCylinderScalingGeometry
public import HeatKernel.Moser.MeanValueNormScaling
public import HeatKernel.Moser.MeanValueCoefficientScaling
import Mathlib.Tactic

/-! # Essential positive-power mean values on arbitrary horizontal cylinders -/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set MeasureTheory TopologicalSpace RothschildStein
open scoped ENNReal
namespace HeatKernel
set_option backward.isDefEq.respectTransparency false

/-- The open-top unit estimate transfers to every horizontal cylinder with its
exact parabolic Jacobian. The constant is independent of the center, radius and
solution. No continuity or preliminary local boundedness is assumed. The
constant may depend on the fixed positive exponent. -/
theorem exists_uniform_signed_matrix_cylinder_positive_power_bound {N q : ℕ}
    (G : HomogeneousGroup N) (hq : q ≤ N) (hqpos : 0 < q)
    (hspan : bracketSpansOn univ (G.horizontalFields hq))
    (hw : ∀ i : Fin q, G.weight (Fin.castLE hq i) = 1)
    {ν p : ℝ} (hν : max 2 (G.homogeneousDimension : ℝ) < ν) (hp : 0 < p)
    (ell upper : ℝ) (hell : 0 < ell) (hupper : 0 ≤ upper) :
    ∃ C : ℝ, 0 < C ∧ ∀ (t₀ : ℝ) (x₀ : Fin N → ℝ) (r : ℝ), 0 < r →
      ∀ (v : ℝ × (Fin N → ℝ) → ℝ)
      (coeff : ℝ → (Fin N → ℝ) → Fin q → Fin q → ℝ),
      IsLocalWeakSolution G hq hqpos hw hspan
        coeff
        ⟨Ioo (t₀ - r ^ 2) t₀, isOpen_Ioo⟩
        ⟨horizontalBall (G.horizontalFields hq) x₀ r,
          isOpen_horizontalBall G hq hqpos hspan x₀ r⟩ (fun t x => v (t, x)) →
      (∀ i j, Measurable (fun z : ℝ × (Fin N → ℝ) => coeff z.1 z.2 i j)) →
      (∀ᵐ z : ℝ × (Fin N → ℝ) ∂volume,
        (∀ i j, coeff z.1 z.2 i j = coeff z.1 z.2 j i) ∧ ∀ ξ : Fin q → ℝ,
          ell * ∑ i, ξ i ^ 2 ≤ ∑ i, ∑ j, coeff z.1 z.2 i j * ξ i * ξ j ∧
          ∑ i, ∑ j, coeff z.1 z.2 i j * ξ i * ξ j ≤ upper * ∑ i, ξ i ^ 2) →
      eLpNormEssSup v (volume.restrict
        (Ioo (t₀ - r ^ 2 / 2) t₀ ×ˢ horizontalBall (G.horizontalFields hq) x₀ (r / 2))) ≤
        ENNReal.ofReal C * (ENNReal.ofReal ((r ^ (G.homogeneousDimension + 2))⁻¹) ^ (1 / p) *
          eLpNorm v (ENNReal.ofReal p) (volume.restrict
            (Ioo (t₀ - r ^ 2) t₀ ×ˢ horizontalBall (G.horizontalFields hq) x₀ r))) := by
  obtain ⟨C, hC, hunit⟩ := exists_uniform_signed_matrix_unit_positive_power_bound G hq hqpos hspan hw hν hp ell upper hell hupper
  refine ⟨C, hC, ?_⟩
  intro t₀ x₀ r hr v coeff hweak ha hbound
  let T := parabolicGroupHomeomorph G t₀ x₀ r hr
  let u := fun t x => v (T (t, x))
  let a := fun t x i j => coeff (T (t, x)).1 (T (t, x)).2 i j
  have hU : CarnotPoint.coordinateBall G hq hqpos hspan (0 : Fin N → ℝ) 1 =
      (⟨horizontalBall (G.horizontalFields hq) 0 1,
        isOpen_horizontalBall G hq hqpos hspan 0 1⟩ : Opens (Fin N → ℝ)) := by
    apply Opens.ext
    exact CarnotPoint.coordinateBall_eq_horizontalBall G hq hqpos hspan (0 : Fin N → ℝ) 1
  have hu := hweak.unit_cylinder_pullback G hq hqpos hw hspan coeff t₀ x₀ r hr
  rw [← hU] at hu
  have hb := hunit u a hu
    (measurable_coefficients_parabolic_pullback G t₀ x₀ r hr ha)
    (ellipticity_coefficients_parabolic_pullback G t₀ x₀ r hr hbound)
  simp only [CarnotPoint.coordinateBall_eq_horizontalBall, Measure.prod_restrict,
    ← Measure.volume_eq_prod] at hb
  let A := Ioo (-1 / 2 : ℝ) 0 ×ˢ horizontalBall (G.horizontalFields hq) 0 (1 / 2)
  let B := Ioo (t₀ - r ^ 2 / 2) t₀ ×ˢ horizontalBall (G.horizontalFields hq) x₀ (r / 2)
  let D := Ioo (-1 : ℝ) 0 ×ˢ horizontalBall (G.horizontalFields hq) 0 1
  let S := Ioo (t₀ - r ^ 2) t₀ ×ˢ horizontalBall (G.horizontalFields hq) x₀ r
  have hi : T ⁻¹' B = A := by
    have he : T '' A = B := by
      simpa only [T, A, B, div_eq_mul_inv, one_mul, neg_one_mul] using
        image_scaled_cylinder_parabolicGroupHomeomorph G hq hw t₀ x₀ r hr (1 / 2) (1 / 2)
    rw [← he]
    exact T.injective.preimage_image _
  have ho : T ⁻¹' S = D := by
    have he : T '' D = S := image_unit_cylinder_parabolicGroupHomeomorph G hq hw t₀ x₀ r hr
    rw [← he]
    exact T.injective.preimage_image _
  change eLpNormEssSup (v ∘ T) (volume.restrict A) ≤
    ENNReal.ofReal C * eLpNorm (v ∘ T) (ENNReal.ofReal p) (volume.restrict D) at hb
  rw [← hi, ← ho,
    eLpNormEssSup_comp_restrict_of_scaled_measure T volume
      (map_parabolicGroupHomeomorph_volume G t₀ x₀ r hr)
      (ENNReal.ofReal_pos.mpr (inv_pos.mpr (pow_pos hr _))).ne',
    eLpNorm_comp_restrict_of_scaled_measure T volume
      (map_parabolicGroupHomeomorph_volume G t₀ x₀ r hr) v S hp] at hb
  exact hb

end HeatKernel
