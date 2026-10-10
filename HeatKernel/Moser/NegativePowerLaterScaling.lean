-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Moser.NegativePowerLaterNormalized
public import HeatKernel.Moser.ReciprocalNormTransport
public import HeatKernel.Moser.MeanValueCylinderScalingGeometry
public import HeatKernel.Moser.WeakSolutionScaling
public import HeatKernel.Moser.MeanValueCoefficientScaling

/-! # Parabolic scaling of later reciprocal bounds -/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set MeasureTheory TopologicalSpace RothschildStein
open scoped ENNReal
namespace HeatKernel

/-- Parabolic coordinates preserve the later reciprocal estimate normalized
by the full reference cylinder. -/
theorem exists_uniform_matrix_later_scaled_reciprocal_constant {N q : ℕ}
    (G : HomogeneousGroup N) (hq : q ≤ N) (hqpos : 0 < q)
    (hspan : bracketSpansOn univ (G.horizontalFields hq))
    (hw : ∀ i : Fin q, G.weight (Fin.castLE hq i) = 1)
    {ν : ℝ} (hν : max 2 (G.homogeneousDimension : ℝ) < ν)
    (ell upper : ℝ) (hell : 0 < ell) (hupper : 0 ≤ upper) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (t : ℝ) (x : Fin N → ℝ) (r : ℝ), 0 < r →
      ∀ (u : ℝ × (Fin N → ℝ) → ℝ),
      Measurable u → (∀ z, 0 ≤ u z) →
      ∀ (coeff : ℝ → (Fin N → ℝ) → Fin q → Fin q → ℝ),
      IsLocalWeakSolution G hq hqpos hw hspan coeff
        ⟨Ioo (t - 4 * r ^ 2) t, isOpen_Ioo⟩
        ⟨horizontalBall (G.horizontalFields hq) x (2 * r),
          isOpen_horizontalBall G hq hqpos hspan x (2 * r)⟩
        (fun t x => u (t, x)) →
      (∀ i j, Measurable (fun z : ℝ × (Fin N → ℝ) => coeff z.1 z.2 i j)) →
      (∀ᵐ z : ℝ × (Fin N → ℝ) ∂volume,
        (∀ i j, coeff z.1 z.2 i j = coeff z.1 z.2 j i) ∧ ∀ ξ : Fin q → ℝ,
          ell * ∑ i, ξ i ^ 2 ≤ ∑ i, ∑ j, coeff z.1 z.2 i j * ξ i * ξ j ∧
          ∑ i, ∑ j, coeff z.1 z.2 i j * ξ i * ξ j ≤ upper * ∑ i, ξ i ^ 2) →
      ∀ ρ R : ℝ, 9 / 10 ≤ ρ → ρ < R → R ≤ 1 →
      ∀ c p : ℝ, 0 < c → 0 < p →
      eLpNormEssSup (fun z => (u z + c)⁻¹)
        (volume.restrict (Ioo (t - r ^ 2 * (3 / 2 * ρ ^ 2)) t ×ˢ
          horizontalBall (G.horizontalFields hq) x (r * (5 / 4 * ρ)))) ≤
        ENNReal.ofReal ((C / (R - ρ) ^ (ν + 2)) ^ (1 / p)) *
          eLpNorm (fun z => (u z + c)⁻¹) (ENNReal.ofReal p)
            (((volume : Measure (ℝ × (Fin N → ℝ)))
              (Ioo (t - r ^ 2 * (3 / 2)) t ×ˢ horizontalBall (G.horizontalFields hq) x (r * (5 / 4))))⁻¹ •
                volume.restrict (Ioo (t - r ^ 2 * (3 / 2 * R ^ 2)) t ×ˢ
                  horizontalBall (G.horizontalFields hq) x (r * (5 / 4 * R)))) := by
  obtain ⟨C, hC, hunit⟩ := exists_uniform_matrix_later_normalized_reciprocal_constant
    G hq hqpos hspan hw hν ell upper hell hupper
  refine ⟨C, hC, ?_⟩
  intro t x r hr u hum hu0 coeff hu ha hbound ρ R hρ hρR hR c p hc hp
  let T := parabolicGroupHomeomorph G t x r hr
  let v := u ∘ T
  let a := fun s y i j => coeff (T (s, y)).1 (T (s, y)).2 i j
  have hv : IsLocalWeakSolution G hq hqpos hw hspan a
      ⟨Ioo (-4 : ℝ) 0, isOpen_Ioo⟩
      (CarnotPoint.coordinateBall G hq hqpos hspan (0 : Fin N → ℝ) 2)
      (fun s y => v (s, y)) := by
    apply IsLocalWeakSolution.parabolic_pullback G hq hqpos hw hspan coeff _ _ hu t x r hr
    · intro s hs
      constructor <;> nlinarith [mul_lt_mul_of_pos_left hs.1 (sq_pos_of_pos hr),
        mul_lt_mul_of_pos_left hs.2 (sq_pos_of_pos hr)]
    · intro y hy
      rw [CarnotPoint.coordinateBall_eq_horizontalBall G hq hqpos hspan
        (0 : Fin N → ℝ) 2] at hy
      change G.mul x (G.dilate r y) ∈ horizontalBall (G.horizontalFields hq) x (2 * r)
      have hball : (fun z => G.mul x (G.dilate r z)) ''
          horizontalBall (G.horizontalFields hq) 0 2 =
            horizontalBall (G.horizontalFields hq) x (2 * r) := by
        rw [← image_image, image_horizontalBall_dilate G hq hw hr, G2.dilate_zero,
          image_horizontalBall_leftTranslation, G2.mul_zero, mul_comm r 2]
      rw [← hball]
      exact ⟨y, hy, rfl⟩
  have hb := hunit v (hum.comp T.measurable) (fun z => hu0 (T z)) a hv
    (measurable_coefficients_parabolic_pullback G t x r hr ha)
    (ellipticity_coefficients_parabolic_pullback G t x r hr hbound)
    ρ R hρ hρR hR c p hc hp
  let S := fun σ : ℝ => Ioo (t - r ^ 2 * (3 / 2 * σ ^ 2)) t ×ˢ
    horizontalBall (G.horizontalFields hq) x (r * (5 / 4 * σ))
  have hpre (σ : ℝ) : T ⁻¹' S σ = Ioo (-3 / 2 * σ ^ 2) 0 ×ˢ
      horizontalBall (G.horizontalFields hq) 0 (5 / 4 * σ) := by
    have he := image_scaled_cylinder_parabolicGroupHomeomorph G hq hw t x r hr
      (3 / 2 * σ ^ 2) (5 / 4 * σ)
    have hn : -(3 / 2 * σ ^ 2) = -3 / 2 * σ ^ 2 := by ring
    rw [hn] at he
    change T ⁻¹' (Ioo (t - r ^ 2 * (3 / 2 * σ ^ 2)) t ×ˢ
      horizontalBall (G.horizontalFields hq) x (r * (5 / 4 * σ))) = _
    rw [← he]
    exact T.injective.preimage_image _
  change eLpNormEssSup ((fun z => (u z + c)⁻¹) ∘ T) _ ≤
    ENNReal.ofReal ((C / (R - ρ) ^ (ν + 2)) ^ (1 / p)) *
      eLpNorm ((fun z => (u z + c)⁻¹) ∘ T) (ENNReal.ofReal p) _ at hb
  rw [← hpre ρ, ← hpre R, ← show T ⁻¹' S 1 =
      Ioo (-3 / 2 : ℝ) 0 ×ˢ horizontalBall (G.horizontalFields hq) 0 (5 / 4) by
        simpa only [one_pow, mul_one] using hpre 1,
    eLpNormEssSup_comp_restrict_of_scaled_measure T volume
      (map_parabolicGroupHomeomorph_volume G t x r hr)
      (ENNReal.ofReal_pos.mpr (inv_pos.mpr (pow_pos hr _))).ne',
    eLpNorm_comp_restrict_normalized_by_reference T volume
      (map_parabolicGroupHomeomorph_volume G t x r hr)
      (ENNReal.ofReal_pos.mpr (inv_pos.mpr (pow_pos hr _))).ne' ENNReal.ofReal_ne_top] at hb
  simpa only [S, one_pow, mul_one] using hb

end HeatKernel
