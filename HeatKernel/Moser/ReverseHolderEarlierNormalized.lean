-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Moser.ReverseHolderEarlierFiniteIteration
public import HeatKernel.Moser.BombieriGiustiHomogeneousCylinderBounds

/-! Normalized reverse-Hölder bounds on the earlier unit cylinders. -/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set MeasureTheory TopologicalSpace RothschildStein
open scoped ENNReal
namespace HeatKernel

/-- The full earlier unit cylinder has finite positive mass. Normalization by
that fixed mass gives the small-positive reverse-Hölder estimate on every pair
of nested earlier cylinders. -/
theorem exists_uniform_matrix_earlier_normalized_reverse_holder_constant {N q : ℕ}
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
      ∀ c p : ℝ, 0 < c → 0 < p → p ≤ 1 / 4 →
      let m := (volume : Measure (ℝ × (Fin N → ℝ)))
        (Ioo (-25 / 8 : ℝ) (-15 / 8) ×ˢ horizontalBall (G.horizontalFields hq) 0 (5 / 4))
      eLpNorm (fun z => u z + c) (ENNReal.ofReal (1 / 2))
        (m⁻¹ • volume.restrict (Ioo (-25 / 8 : ℝ) (-25 / 8 + 5 / 4 * ρ ^ 2) ×ˢ
          horizontalBall (G.horizontalFields hq) 0 (5 / 4 * ρ))) ≤
        ENNReal.ofReal ((C / (R - ρ) ^ (2 * (ν + 2))) ^ (1 / p - 1 / (1 / 2))) *
          eLpNorm (fun z => u z + c) (ENNReal.ofReal p)
            (m⁻¹ • volume.restrict (Ioo (-25 / 8 : ℝ) (-25 / 8 + 5 / 4 * R ^ 2) ×ˢ
              horizontalBall (G.horizontalFields hq) 0 (5 / 4 * R))) := by
  let m := (volume : Measure (ℝ × (Fin N → ℝ)))
    (Ioo (-25 / 8 : ℝ) (-15 / 8) ×ˢ horizontalBall (G.horizontalFields hq) 0 (5 / 4))
  have hm : 0 < m ∧ m < ⊤ := by
    have hm := measure_horizontal_product_cylinder_pos_finite G hq hqpos hspan hw
      (0 : Fin N → ℝ) (by norm_num : (-25 / 8 : ℝ) < -15 / 8)
      (by norm_num : (0 : ℝ) < 5 / 4)
    rw [show @Metric.ball (CarnotPoint G hq hqpos hspan) _ (0 : Fin N → ℝ) (5 / 4) =
      horizontalBall (G.horizontalFields hq) 0 (5 / 4) from
        CarnotPoint.coordinateBall_eq_horizontalBall G hq hqpos hspan
          (0 : Fin N → ℝ) (5 / 4)] at hm
    exact hm
  have href : ((volume.restrict (Icc (-25 / 8 : ℝ) (-15 / 8))).prod
      (volume.restrict (CarnotPoint.coordinateBall G hq hqpos hspan
        (0 : Fin N → ℝ) (5 / 4) : Set (Fin N → ℝ)))) univ = m := by
    rw [← restrict_Ioo_eq_restrict_Icc,
      CarnotPoint.coordinateBall_eq_horizontalBall G hq hqpos hspan
        (0 : Fin N → ℝ) (5 / 4), Measure.prod_restrict, ← Measure.volume_eq_prod,
      Measure.restrict_apply_univ]
  obtain ⟨C, hC, hfinite⟩ := exists_uniform_matrix_earlier_finite_constant_of_reference_mass
    G hq hqpos hspan hw hν ell upper hell hupper m hm.1.ne' hm.2.ne href.le
  refine ⟨C, hC, ?_⟩
  intro u hum hu0 coeff hu ha hbound ρ R hρ hρR hR c p hc hp hp4
  have hb := hfinite u hum hu0 coeff hu ha hbound ρ R hρ hρR hR c p hc hp hp4
  rw [CarnotPoint.coordinateBall_eq_horizontalBall G hq hqpos hspan
    (0 : Fin N → ℝ) (5 / 4 * ρ),
    CarnotPoint.coordinateBall_eq_horizontalBall G hq hqpos hspan
      (0 : Fin N → ℝ) (5 / 4 * R)] at hb
  simpa only [← restrict_Ioo_eq_restrict_Icc, Measure.prod_restrict,
    ← Measure.volume_eq_prod] using hb

end HeatKernel
