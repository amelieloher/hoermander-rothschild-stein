-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Moser.NegativePowerLaterOpen
public import HeatKernel.Moser.ReciprocalNormTransport
public import HeatKernel.Moser.BombieriGiustiHomogeneousCylinderBounds

/-! # Normalized reciprocal bounds on unit later cylinders -/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set MeasureTheory TopologicalSpace RothschildStein
open scoped ENNReal
namespace HeatKernel

/-- A fixed reference mass normalizes the reciprocal later-cylinder estimate,
with a constant uniform over all positive exponents and all nested radii. -/
theorem exists_uniform_matrix_later_normalized_reciprocal_constant {N q : ℕ}
    (G : HomogeneousGroup N) (hq : q ≤ N) (hqpos : 0 < q)
    (hspan : bracketSpansOn univ (G.horizontalFields hq))
    (hw : ∀ i : Fin q, G.weight (Fin.castLE hq i) = 1)
    {ν : ℝ} (hν : max 2 (G.homogeneousDimension : ℝ) < ν)
    (ell upper : ℝ) (hell : 0 < ell) (hupper : 0 ≤ upper) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (u : ℝ × (Fin N → ℝ) → ℝ),
      Measurable u → (∀ z, 0 ≤ u z) →
      ∀ (coeff : ℝ → (Fin N → ℝ) → Fin q → Fin q → ℝ),
      IsLocalWeakSolution G hq hqpos hw hspan coeff
        ⟨Ioo (-4 : ℝ) 0, isOpen_Ioo⟩
        (CarnotPoint.coordinateBall G hq hqpos hspan (0 : Fin N → ℝ) 2)
        (fun t x => u (t, x)) →
      (∀ i j, Measurable (fun z : ℝ × (Fin N → ℝ) => coeff z.1 z.2 i j)) →
      (∀ᵐ z : ℝ × (Fin N → ℝ) ∂volume,
        (∀ i j, coeff z.1 z.2 i j = coeff z.1 z.2 j i) ∧ ∀ ξ : Fin q → ℝ,
          ell * ∑ i, ξ i ^ 2 ≤ ∑ i, ∑ j, coeff z.1 z.2 i j * ξ i * ξ j ∧
          ∑ i, ∑ j, coeff z.1 z.2 i j * ξ i * ξ j ≤ upper * ∑ i, ξ i ^ 2) →
      ∀ ρ R : ℝ, 9 / 10 ≤ ρ → ρ < R → R ≤ 1 →
      ∀ c p : ℝ, 0 < c → 0 < p →
      eLpNormEssSup (fun z => (u z + c)⁻¹)
        (volume.restrict (Ioo (-3 / 2 * ρ ^ 2) 0 ×ˢ
          horizontalBall (G.horizontalFields hq) 0 (5 / 4 * ρ))) ≤
        ENNReal.ofReal ((C / (R - ρ) ^ (ν + 2)) ^ (1 / p)) *
          eLpNorm (fun z => (u z + c)⁻¹) (ENNReal.ofReal p)
            (((volume : Measure (ℝ × (Fin N → ℝ)))
              (Ioo (-3 / 2 : ℝ) 0 ×ˢ horizontalBall (G.horizontalFields hq) 0 (5 / 4)))⁻¹ •
                volume.restrict (Ioo (-3 / 2 * R ^ 2) 0 ×ˢ
                  horizontalBall (G.horizontalFields hq) 0 (5 / 4 * R))) := by
  obtain ⟨L, hL, hopen⟩ := exists_uniform_matrix_later_open_reciprocal_constant
    G hq hqpos hspan hw hν ell upper hell hupper
  let m := (volume : Measure (ℝ × (Fin N → ℝ)))
    (Ioo (-3 / 2 : ℝ) 0 ×ˢ horizontalBall (G.horizontalFields hq) 0 (5 / 4))
  have hm : 0 < m ∧ m < ⊤ := by
    have hm := measure_horizontal_product_cylinder_pos_finite G hq hqpos hspan hw (0 : Fin N → ℝ)
      (by norm_num : (-3 / 2 : ℝ) < 0) (by norm_num : (0 : ℝ) < 5 / 4)
    rw [show @Metric.ball (CarnotPoint G hq hqpos hspan) _
      (0 : Fin N → ℝ) (5 / 4) = horizontalBall (G.horizontalFields hq) 0 (5 / 4) from
        CarnotPoint.coordinateBall_eq_horizontalBall G hq hqpos hspan
          (0 : Fin N → ℝ) (5 / 4)] at hm
    exact hm
  let C := max 1 (L * m.toReal)
  refine ⟨C, le_max_left _ _, ?_⟩
  intro u hum hu0 coeff hu ha hbound ρ R hρ hρR hR c p hc hp
  have hb := hopen u hum hu0 coeff hu ha hbound ρ R hρ hρR hR c p hc hp
  rw [CarnotPoint.coordinateBall_eq_horizontalBall G hq hqpos hspan
    (0 : Fin N → ℝ) (5 / 4 * ρ),
    CarnotPoint.coordinateBall_eq_horizontalBall G hq hqpos hspan
      (0 : Fin N → ℝ) (5 / 4 * R)] at hb
  simp only [Measure.prod_restrict, ← Measure.volume_eq_prod] at hb
  exact reciprocal_norm_bound_normalized_by_reference _ _ _ hp (by linarith : 0 ≤ L)
    (sub_pos.mpr hρR) hm.1.ne' hm.2.ne (le_max_right _ _) hb

end HeatKernel
