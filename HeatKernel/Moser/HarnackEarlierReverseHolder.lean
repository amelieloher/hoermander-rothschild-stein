-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Moser.ReverseHolderEarlierScaling
public import HeatKernel.Moser.ReverseHolderMomentNormalization
public import HeatKernel.Moser.WeakSolutionRepresentativeCongruence
public import HeatKernel.Moser.BombieriGiustiCylinders

/-! Uniform reverse-Hölder estimates on earlier Harnack cylinders. -/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set MeasureTheory TopologicalSpace RothschildStein
open scoped ENNReal
namespace HeatKernel

/-- Uniformly elliptic matrix weak solutions satisfy the small-positive-power
reverse-Hölder family on earlier Harnack cylinders. The endpoint is one half;
the constants precede the cylinder, solution, perturbation, and initial power. -/
theorem exists_uniform_matrix_harnackEarlier_reverseHolder_family
    {N q : ℕ} (G : HomogeneousGroup N) (hq : q ≤ N) (hqpos : 0 < q)
    (hspan : bracketSpansOn univ (G.horizontalFields hq))
    (hw : ∀ i : Fin q, G.weight (Fin.castLE hq i) = 1)
    (ell upper : ℝ) (hell : 0 < ell) (hupper : 0 ≤ upper) :
    ∃ p₀ Cminus κminus : ℝ,
      0 < p₀ ∧ p₀ ≤ 2 ∧ 1 ≤ Cminus ∧ 0 ≤ κminus ∧
      ∀ (x : CarnotPoint G hq hqpos hspan) (t r : ℝ), 0 < r →
      ∀ (coeff : ℝ → (Fin N → ℝ) → Fin q → Fin q → ℝ)
      (u : ℝ × CarnotPoint G hq hqpos hspan → ℝ), Measurable u →
      (∀ᵐ y ∂(volume.prod (CarnotPoint.volume G hq hqpos hspan)).restrict
        (Ioo (t - 4 * r ^ 2) t ×ˢ Metric.ball x (2 * r)), 0 ≤ u y) →
      IsLocalWeakSolution G hq hqpos hw hspan coeff
        ⟨Ioo (t - 4 * r ^ 2) t, isOpen_Ioo⟩
        ⟨horizontalBall (G.horizontalFields hq) x (2 * r),
          isOpen_horizontalBall G hq hqpos hspan x (2 * r)⟩
        (fun s y => u (s, y)) →
      (∀ i j, Measurable (fun z : ℝ × (Fin N → ℝ) => coeff z.1 z.2 i j)) →
      (∀ᵐ z : ℝ × (Fin N → ℝ) ∂volume,
        (∀ i j, coeff z.1 z.2 i j = coeff z.1 z.2 j i) ∧ ∀ ξ : Fin q → ℝ,
          ell * ∑ i, ξ i ^ 2 ≤ ∑ i, ∑ j, coeff z.1 z.2 i j * ξ i * ξ j ∧
          ∑ i, ∑ j, coeff z.1 z.2 i j * ξ i * ξ j ≤ upper * ∑ i, ξ i ^ 2) →
      ∀ ε : ℝ, 0 < ε →
      ∀ σ' σ'' : ℝ, 31 / 32 ≤ σ' → σ' < σ'' → σ'' ≤ 1 →
      ∀ p : ℝ, 0 < p → p ≤ p₀ / 2 →
      let μ := volume.prod (CarnotPoint.volume G hq hqpos hspan)
      (∫⁻ y in harnackEarlierIterationCylinder x t r σ',
        ENNReal.ofReal (u y + ε) ^ p₀ ∂μ) ^ (1 / p₀) ≤
        (ENNReal.ofReal (Cminus * (1 / (σ'' - σ')) ^ κminus) *
          (μ (harnackEarlierIterationCylinder x t r 1))⁻¹) ^ (1 / p - 1 / p₀) *
            (∫⁻ y in harnackEarlierIterationCylinder x t r σ'',
              ENNReal.ofReal (u y + ε) ^ p ∂μ) ^ (1 / p) := by
  let ν := max 2 (G.homogeneousDimension : ℝ) + 1
  have hν : max 2 (G.homogeneousDimension : ℝ) < ν := by dsimp only [ν]; linarith
  have hν0 : 0 < ν := by dsimp only [ν]; linarith [le_max_left 2 (G.homogeneousDimension : ℝ)]
  obtain ⟨C, hC, hscaled⟩ := exists_uniform_matrix_earlier_scaled_reverse_holder_constant
    G hq hqpos hspan hw hν ell upper hell hupper
  refine ⟨1 / 2, C, 2 * (ν + 2), by norm_num, by norm_num, hC, by positivity, ?_⟩
  intro x t r hr coeff u hum hu0 hu ha hbound c hc ρ R hρ hρR hR p hp hp4
  let v := fun z => max (u z) 0
  have hball (s : ℝ) : @Metric.ball (CarnotPoint G hq hqpos hspan) _ x s =
      horizontalBall (G.horizontalFields hq) x s :=
    CarnotPoint.coordinateBall_eq_horizontalBall G hq hqpos hspan x s
  have hn : ∀ᵐ z : ℝ × (Fin N → ℝ) ∂volume.restrict
      (Ioo (t - 4 * r ^ 2) t ×ˢ horizontalBall (G.horizontalFields hq) x (2 * r)), 0 ≤ u z := by
    have hn := hu0
    rw [hball] at hn
    exact hn
  have hvweak := hu.max_zero_of_ae_nonneg hn
  have hv := hscaled t x r hr v (hum.max measurable_const) (fun z => le_max_right _ _)
    coeff hvweak ha hbound ρ R (by linarith) hρR hR c p hc hp (by linarith)
  have hset (σ : ℝ) :
      Ioo (t + r ^ 2 * (-25 / 8)) (t + r ^ 2 * (-25 / 8 + 5 / 4 * σ ^ 2)) ×ˢ
        horizontalBall (G.horizontalFields hq) x (r * (5 / 4 * σ)) =
          harnackEarlierIterationCylinder x t r σ := by
    rw [harnackEarlierIterationCylinder, hball]
    congr 2 <;> ring
  have href : Ioo (t + r ^ 2 * (-25 / 8)) (t + r ^ 2 * (-15 / 8)) ×ˢ
      horizontalBall (G.horizontalFields hq) x (r * (5 / 4)) =
        harnackEarlierIterationCylinder x t r 1 := by
    simpa only [one_pow, mul_one,
      show (-25 / 8 + 5 / 4 : ℝ) = -15 / 8 by norm_num] using hset 1
  rw [hset ρ, hset R, href] at hv
  let μ : Measure (ℝ × CarnotPoint G hq hqpos hspan) :=
    volume.prod (CarnotPoint.volume G hq hqpos hspan)
  have hsub (σ : ℝ) (hσ0 : 0 ≤ σ) (hσ : σ ≤ 1) :
      harnackEarlierIterationCylinder x t r σ ⊆
        Ioo (t - 4 * r ^ 2) t ×ˢ Metric.ball x (2 * r) := by
    intro z hz
    have hsq : σ ^ 2 ≤ 1 := by nlinarith
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · exact lt_trans (by nlinarith [sq_pos_of_pos hr] :
        t - 4 * r ^ 2 < t - 25 / 8 * r ^ 2) hz.1.1
    · exact lt_of_lt_of_le hz.1.2 (by
        nlinarith [mul_le_mul_of_nonneg_right hsq (sq_nonneg r)])
    · exact Metric.ball_subset_ball (show 5 / 4 * σ * r ≤ 2 * r by
        nlinarith [mul_le_mul_of_nonneg_right hσ hr.le]) hz.2
  have hρ0 : 0 ≤ ρ := by linarith
  have hR0 : 0 ≤ R := by linarith
  have hρone : ρ ≤ 1 := hρR.le.trans hR
  have heq (σ : ℝ) (hσ0 : 0 ≤ σ) (hσ : σ ≤ 1) :
      (fun z => v z + c) =ᵐ[μ.restrict (harnackEarlierIterationCylinder x t r σ)]
        (fun z => u z + c) := by
    filter_upwards [ae_restrict_of_ae_restrict_of_subset (hsub σ hσ0 hσ) hu0] with z hz
    simp only [v, max_eq_left hz]
  change eLpNorm (fun z => v z + c) (ENNReal.ofReal (1 / 2))
      ((μ (harnackEarlierIterationCylinder x t r 1))⁻¹ •
        μ.restrict (harnackEarlierIterationCylinder x t r ρ)) ≤
    ENNReal.ofReal ((C / (R - ρ) ^ (2 * (ν + 2))) ^ (1 / p - 1 / (1 / 2))) *
      eLpNorm (fun z => v z + c) (ENNReal.ofReal p)
        ((μ (harnackEarlierIterationCylinder x t r 1))⁻¹ •
          μ.restrict (harnackEarlierIterationCylinder x t r R)) at hv
  rw [eLpNorm_congr_ae (Measure.ae_smul_measure (heq ρ hρ0 hρone) _),
    eLpNorm_congr_ae (Measure.ae_smul_measure (heq R hR0 hR) _)] at hv
  have hmref : 0 < μ (harnackEarlierIterationCylinder x t r 1) ∧
      μ (harnackEarlierIterationCylinder x t r 1) < ⊤ := by
    have hm := measure_horizontal_product_cylinder_pos_finite G hq hqpos hspan hw x
      (show t - 25 / 8 * r ^ 2 < t - 15 / 8 * r ^ 2 by nlinarith [sq_pos_of_pos hr])
      (show 0 < 5 / 4 * r by positivity)
    have hs : harnackEarlierIterationCylinder x t r 1 =
        Ioo (t - 25 / 8 * r ^ 2) (t - 15 / 8 * r ^ 2) ×ˢ Metric.ball x (5 / 4 * r) := by
      rw [harnackEarlierIterationCylinder]
      congr 2 <;> ring
    simpa only [hs] using hm
  have hmoment := reverse_holder_normalized_norm_bound_to_moments μ _ _ hum hc hp
    (by norm_num : (0 : ℝ) < 1 / 2) (by linarith) (by positivity)
    hmref.1.ne' hmref.2.ne
    (ae_restrict_of_ae_restrict_of_subset (hsub ρ hρ0 hρone) hu0)
    (ae_restrict_of_ae_restrict_of_subset (hsub R hR0 hR) hu0) hv
  have he : C / (R - ρ) ^ (2 * (ν + 2)) = C * (1 / (R - ρ)) ^ (2 * (ν + 2)) := by
    rw [one_div, Real.inv_rpow (sub_pos.mpr hρR).le, div_eq_mul_inv]
  simpa only [he] using hmoment

end HeatKernel
