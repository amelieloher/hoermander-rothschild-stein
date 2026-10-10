-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Moser.MeanValueSignedMatrixNestedUnit
import Mathlib.Tactic

/-! # Normalized elliptic matrix mean values for arbitrary fixed cylinder shapes -/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set MeasureTheory TopologicalSpace RothschildStein
open scoped ENNReal
namespace HeatKernel
set_option backward.isDefEq.respectTransparency false

/-- Every fixed positive aspect ratio and strictly smaller inner time and radius
factors give a normalized mean-value estimate for every fixed positive power.
The constant is independent of the center, scale, top time and signed uniformly elliptic matrix weak solution. Both cylinders share the open top. -/
theorem exists_uniform_signed_matrix_nested_cylinder_positive_power_mean_value {N q : ℕ}
    (G : HomogeneousGroup N) (hq : q ≤ N) (hqpos : 0 < q)
    (hspan : bracketSpansOn univ (G.horizontalFields hq))
    (hw : ∀ i : Fin q, G.weight (Fin.castLE hq i) = 1)
    {p τ θ ρ : ℝ} (hp : 0 < p) (hτ : 0 < τ) (hθτ : θ < τ) (hρone : ρ < 1)
    (ell upper : ℝ) (hell : 0 < ell) (hupper : 0 ≤ upper) :
    ∃ C : ℝ, 0 < C ∧ ∀ (t₀ : ℝ) (x₀ : Fin N → ℝ) (r : ℝ), 0 < r →
      ∀ (v : ℝ × (Fin N → ℝ) → ℝ)
      (coeff : ℝ → (Fin N → ℝ) → Fin q → Fin q → ℝ),
      IsLocalWeakSolution G hq hqpos hw hspan
        coeff
        ⟨Ioo (t₀ - r ^ 2 * τ) t₀, isOpen_Ioo⟩
        ⟨horizontalBall (G.horizontalFields hq) x₀ r,
          isOpen_horizontalBall G hq hqpos hspan x₀ r⟩ (fun t x => v (t, x)) →
      (∀ i j, Measurable (fun z : ℝ × (Fin N → ℝ) => coeff z.1 z.2 i j)) →
      (∀ᵐ z : ℝ × (Fin N → ℝ) ∂volume,
        (∀ i j, coeff z.1 z.2 i j = coeff z.1 z.2 j i) ∧ ∀ ξ : Fin q → ℝ,
          ell * ∑ i, ξ i ^ 2 ≤ ∑ i, ∑ j, coeff z.1 z.2 i j * ξ i * ξ j ∧
          ∑ i, ∑ j, coeff z.1 z.2 i j * ξ i * ξ j ≤ upper * ∑ i, ξ i ^ 2) →
      eLpNormEssSup v (volume.restrict
        (Ioo (t₀ - r ^ 2 * θ) t₀ ×ˢ horizontalBall (G.horizontalFields hq) x₀ (r * ρ))) ≤
        ENNReal.ofReal C * eLpNorm v (ENNReal.ofReal p)
          (((volume : Measure (ℝ × (Fin N → ℝ)))
            (Ioo (t₀ - r ^ 2 * τ) t₀ ×ˢ horizontalBall (G.horizontalFields hq) x₀ r))⁻¹ •
              volume.restrict (Ioo (t₀ - r ^ 2 * τ) t₀ ×ˢ horizontalBall (G.horizontalFields hq) x₀ r)) := by
  obtain ⟨C, hC, hunit⟩ := exists_uniform_signed_matrix_nested_unit_positive_power_mean_value
    G hq hqpos hspan hw hp hτ hθτ hρone ell upper hell hupper
  refine ⟨C, hC, ?_⟩
  intro t₀ x₀ r hr v coeff hweak ha hbound
  let T := parabolicGroupHomeomorph G t₀ x₀ r hr
  let u := v ∘ T
  let a := fun t x i j => coeff (T (t, x)).1 (T (t, x)).2 i j
  have hTtime (t : ℝ) (ht : t ∈ Ioo (-τ) 0) :
      t₀ + r ^ 2 * t ∈ Ioo (t₀ - r ^ 2 * τ) t₀ := by
    constructor <;> nlinarith [mul_lt_mul_of_pos_left ht.1 (sq_pos_of_pos hr),
      mul_lt_mul_of_pos_left ht.2 (sq_pos_of_pos hr)]
  have huweak : IsLocalWeakSolution G hq hqpos hw hspan
      a
      ⟨Ioo (-τ) 0, isOpen_Ioo⟩
      ⟨horizontalBall (G.horizontalFields hq) 0 1,
        isOpen_horizontalBall G hq hqpos hspan 0 1⟩ (fun t x => u (t, x)) := by
    apply IsLocalWeakSolution.parabolic_pullback G hq hqpos hw hspan
      coeff _ _ hweak t₀ x₀ r hr
    · exact hTtime
    · intro x hx
      change G.mul x₀ (G.dilate r x) ∈ horizontalBall (G.horizontalFields hq) x₀ r
      rw [horizontalBall_eq_image_unitBall G hq hw hr x₀]
      exact ⟨x, hx, rfl⟩
  have hb := hunit u a huweak
    (measurable_coefficients_parabolic_pullback G t₀ x₀ r hr ha)
    (ellipticity_coefficients_parabolic_pullback G t₀ x₀ r hr hbound)
  let A := Ioo (-θ) 0 ×ˢ horizontalBall (G.horizontalFields hq) 0 ρ
  let B := Ioo (t₀ - r ^ 2 * θ) t₀ ×ˢ horizontalBall (G.horizontalFields hq) x₀ (r * ρ)
  let D := Ioo (-τ) 0 ×ˢ horizontalBall (G.horizontalFields hq) 0 1
  let S := Ioo (t₀ - r ^ 2 * τ) t₀ ×ˢ horizontalBall (G.horizontalFields hq) x₀ r
  have hi : T ⁻¹' B = A := by
    have he : T '' A = B := image_scaled_cylinder_parabolicGroupHomeomorph G hq hw t₀ x₀ r hr θ ρ
    rw [← he]
    exact T.injective.preimage_image _
  have ho : T ⁻¹' S = D := by
    have he : T '' D = S := by
      simpa only [mul_one] using image_scaled_cylinder_parabolicGroupHomeomorph G hq hw t₀ x₀ r hr τ 1
    rw [← he]
    exact T.injective.preimage_image _
  change eLpNormEssSup (v ∘ T) (volume.restrict A) ≤
    ENNReal.ofReal C * eLpNorm (v ∘ T) (ENNReal.ofReal p)
      ((volume D)⁻¹ • volume.restrict D) at hb
  rw [← hi, ← ho, eLpNormEssSup_comp_restrict_of_scaled_measure T volume
    (map_parabolicGroupHomeomorph_volume G t₀ x₀ r hr)
    (ENNReal.ofReal_pos.mpr (inv_pos.mpr (pow_pos hr _))).ne',
    eLpNorm_normalized_comp_restrict_of_scaled_measure T volume
      (map_parabolicGroupHomeomorph_volume G t₀ x₀ r hr)
      (ENNReal.ofReal_pos.mpr (inv_pos.mpr (pow_pos hr _))).ne' ENNReal.ofReal_ne_top] at hb
  exact hb

end HeatKernel
