-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Moser.ReverseHolderEarlierNormalized
public import HeatKernel.Moser.ReciprocalNormTransport
public import HeatKernel.Moser.MeanValueCylinderScalingGeometry
public import HeatKernel.Moser.WeakSolutionScaling
public import HeatKernel.Moser.MeanValueCoefficientScaling

/-! Parabolic scaling of finite reverse-Hölder bounds. -/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set MeasureTheory TopologicalSpace RothschildStein
open scoped ENNReal
namespace HeatKernel

/-- Parabolic coordinates scale both endpoints of an interior time interval
and the radius of its horizontal spatial ball. -/
theorem image_interior_cylinder_parabolicGroupHomeomorph {N q : ℕ}
    (G : HomogeneousGroup N) (hq : q ≤ N)
    (hw : ∀ i : Fin q, G.weight (Fin.castLE hq i) = 1)
    (t₀ : ℝ) (x₀ : Fin N → ℝ) (r : ℝ) (hr : 0 < r) (a b ρ : ℝ) :
    parabolicGroupHomeomorph G t₀ x₀ r hr ''
      (Ioo a b ×ˢ horizontalBall (G.horizontalFields hq) 0 ρ) =
        Ioo (t₀ + r ^ 2 * a) (t₀ + r ^ 2 * b) ×ˢ
          horizontalBall (G.horizontalFields hq) x₀ (r * ρ) := by
  have hball : (fun y => G.mul x₀ (G.dilate r y)) ''
      horizontalBall (G.horizontalFields hq) 0 ρ =
        horizontalBall (G.horizontalFields hq) x₀ (r * ρ) := by
    rw [← image_image, image_horizontalBall_dilate G hq hw hr,
      G2.dilate_zero, image_horizontalBall_leftTranslation, G2.mul_zero]
  ext z
  constructor
  · rintro ⟨y, hy, rfl⟩
    refine ⟨?_, ?_⟩
    · simp only [parabolicGroupHomeomorph_apply]
      constructor <;> nlinarith [mul_lt_mul_of_pos_left hy.1.1 (sq_pos_of_pos hr),
        mul_lt_mul_of_pos_left hy.1.2 (sq_pos_of_pos hr)]
    · rw [← hball]
      exact ⟨y.2, hy.2, rfl⟩
  · intro hz
    rw [← hball] at hz
    obtain ⟨y, hy, heq⟩ := hz.2
    refine ⟨((z.1 - t₀) / r ^ 2, y), ⟨?_, hy⟩, ?_⟩
    · constructor
      · exact (lt_div_iff₀ (sq_pos_of_pos hr)).mpr (by linarith [hz.1.1])
      · exact (div_lt_iff₀ (sq_pos_of_pos hr)).mpr (by linarith [hz.1.2])
    · apply Prod.ext
      · simp only [parabolicGroupHomeomorph_apply]
        field_simp
        ring
      · exact heq

/-- The earlier reverse-Hölder estimate is unchanged by parabolic coordinates
when both norms use the mass of the full earlier reference cylinder. -/
theorem exists_uniform_matrix_earlier_scaled_reverse_holder_constant {N q : ℕ}
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
      ∀ c p : ℝ, 0 < c → 0 < p → p ≤ 1 / 4 →
      let m := (volume : Measure (ℝ × (Fin N → ℝ)))
        (Ioo (t + r ^ 2 * (-25 / 8)) (t + r ^ 2 * (-15 / 8)) ×ˢ
          horizontalBall (G.horizontalFields hq) x (r * (5 / 4)))
      eLpNorm (fun z => u z + c) (ENNReal.ofReal (1 / 2))
        (m⁻¹ • volume.restrict
          (Ioo (t + r ^ 2 * (-25 / 8)) (t + r ^ 2 * (-25 / 8 + 5 / 4 * ρ ^ 2)) ×ˢ
            horizontalBall (G.horizontalFields hq) x (r * (5 / 4 * ρ)))) ≤
        ENNReal.ofReal ((C / (R - ρ) ^ (2 * (ν + 2))) ^ (1 / p - 1 / (1 / 2))) *
          eLpNorm (fun z => u z + c) (ENNReal.ofReal p)
            (m⁻¹ • volume.restrict
              (Ioo (t + r ^ 2 * (-25 / 8)) (t + r ^ 2 * (-25 / 8 + 5 / 4 * R ^ 2)) ×ˢ
                horizontalBall (G.horizontalFields hq) x (r * (5 / 4 * R)))) := by
  obtain ⟨C, hC, hunit⟩ := exists_uniform_matrix_earlier_normalized_reverse_holder_constant
    G hq hqpos hspan hw hν ell upper hell hupper
  refine ⟨C, hC, ?_⟩
  intro t x r hr u hum hu0 coeff hu ha hbound ρ R hρ hρR hR c p hc hp hp4
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
    ρ R hρ hρR hR c p hc hp hp4
  let S := fun σ : ℝ =>
    Ioo (t + r ^ 2 * (-25 / 8)) (t + r ^ 2 * (-25 / 8 + 5 / 4 * σ ^ 2)) ×ˢ
      horizontalBall (G.horizontalFields hq) x (r * (5 / 4 * σ))
  have hpre (σ : ℝ) : T ⁻¹' S σ =
      Ioo (-25 / 8 : ℝ) (-25 / 8 + 5 / 4 * σ ^ 2) ×ˢ
        horizontalBall (G.horizontalFields hq) 0 (5 / 4 * σ) := by
    have he := image_interior_cylinder_parabolicGroupHomeomorph G hq hw t x r hr
      (-25 / 8) (-25 / 8 + 5 / 4 * σ ^ 2) (5 / 4 * σ)
    change T ⁻¹' (Ioo _ _ ×ˢ horizontalBall _ x _) = _
    rw [← he]
    exact T.injective.preimage_image _
  have href : T ⁻¹' S 1 = Ioo (-25 / 8 : ℝ) (-15 / 8) ×ˢ
      horizontalBall (G.horizontalFields hq) 0 (5 / 4) := by
    simpa only [one_pow, mul_one,
      show (-25 / 8 + 5 / 4 : ℝ) = -15 / 8 by norm_num] using hpre 1
  change eLpNorm ((fun z => u z + c) ∘ T) (ENNReal.ofReal (1 / 2)) _ ≤
    ENNReal.ofReal ((C / (R - ρ) ^ (2 * (ν + 2))) ^ (1 / p - 1 / (1 / 2))) *
      eLpNorm ((fun z => u z + c) ∘ T) (ENNReal.ofReal p) _ at hb
  rw [← hpre ρ, ← hpre R, ← href,
    eLpNorm_comp_restrict_normalized_by_reference T volume
      (map_parabolicGroupHomeomorph_volume G t x r hr)
      (ENNReal.ofReal_pos.mpr (inv_pos.mpr (pow_pos hr _))).ne' ENNReal.ofReal_ne_top,
    eLpNorm_comp_restrict_normalized_by_reference T volume
      (map_parabolicGroupHomeomorph_volume G t x r hr)
      (ENNReal.ofReal_pos.mpr (inv_pos.mpr (pow_pos hr _))).ne' ENNReal.ofReal_ne_top] at hb
  simpa only [S, one_pow, mul_one,
    show (-25 / 8 + 5 / 4 : ℝ) = -15 / 8 by norm_num] using hb

end HeatKernel
