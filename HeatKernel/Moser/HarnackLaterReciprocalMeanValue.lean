-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Moser.NegativePowerLaterScaling
public import HeatKernel.Moser.WeakSolutionRepresentativeCongruence
public import HeatKernel.Moser.BombieriGiustiCylinders

/-! # Uniform reciprocal mean values on later Harnack cylinders -/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set MeasureTheory TopologicalSpace RothschildStein
open scoped ENNReal
namespace HeatKernel

/-- One constant pair gives the reciprocal mean-value bound for every positive
power on later Harnack cylinders. The cylinders have open top time and use the
full reference cylinder for normalization. -/
theorem exists_uniform_matrix_harnackLater_reciprocal_mean_value
    {N q : ℕ} (G : HomogeneousGroup N) (hq : q ≤ N) (hqpos : 0 < q)
    (hspan : bracketSpansOn univ (G.horizontalFields hq))
    (hw : ∀ i : Fin q, G.weight (Fin.castLE hq i) = 1)
    (ell upper : ℝ) (hell : 0 < ell) (hupper : 0 ≤ upper) :
    ∃ Cplus κplus : ℝ, 1 ≤ Cplus ∧ 0 ≤ κplus ∧
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
      ∀ σ' σ'' : ℝ, 9 / 10 ≤ σ' → σ' < σ'' → σ'' ≤ 1 →
      ∀ p : ℝ, 0 < p →
      let μ : Measure (ℝ × CarnotPoint G hq hqpos hspan) := volume.prod (CarnotPoint.volume G hq hqpos hspan)
      essSup (fun y => ENNReal.ofReal (1 / (u y + ε)))
        (μ.restrict (harnackLaterIterationCylinder x t r σ')) ≤
        (ENNReal.ofReal (Cplus * (1 / (σ'' - σ')) ^ κplus) *
          (μ (harnackLaterIterationCylinder x t r 1))⁻¹ *
            (∫⁻ y in harnackLaterIterationCylinder x t r σ'',
              ENNReal.ofReal (1 / (u y + ε)) ^ p ∂μ)) ^ (1 / p) := by
  let ν := max 2 (G.homogeneousDimension : ℝ) + 1
  have hν : max 2 (G.homogeneousDimension : ℝ) < ν := by dsimp only [ν]; linarith
  have hν0 : 0 < ν := by dsimp only [ν]; linarith [le_max_left 2 (G.homogeneousDimension : ℝ)]
  obtain ⟨C, hC, hscaled⟩ := exists_uniform_matrix_later_scaled_reciprocal_constant
    G hq hqpos hspan hw hν ell upper hell hupper
  refine ⟨C, ν + 2, hC, by positivity, ?_⟩
  intro x t r hr coeff u hum hu0 hu ha hbound c hc ρ R hρ hρR hR p hp
  let v := fun z => max (u z) 0
  have hball (s : ℝ) : @Metric.ball (CarnotPoint G hq hqpos hspan) _ x s =
      horizontalBall (G.horizontalFields hq) x s := by
    exact CarnotPoint.coordinateBall_eq_horizontalBall G hq hqpos hspan x s
  have hn : ∀ᵐ z : ℝ × (Fin N → ℝ) ∂volume.restrict
      (Ioo (t - 4 * r ^ 2) t ×ˢ horizontalBall (G.horizontalFields hq) x (2 * r)),
      0 ≤ u z := by
    have hn := hu0
    rw [hball] at hn
    exact hn
  have hvweak := hu.max_zero_of_ae_nonneg hn
  have hv := hscaled t x r hr v (hum.max measurable_const) (fun z => le_max_right _ _)
    coeff hvweak ha hbound ρ R hρ hρR hR c p hc hp
  have hset (σ : ℝ) : Ioo (t - r ^ 2 * (3 / 2 * σ ^ 2)) t ×ˢ
      horizontalBall (G.horizontalFields hq) x (r * (5 / 4 * σ)) =
        harnackLaterIterationCylinder x t r σ := by
    rw [harnackLaterIterationCylinder, hball]
    congr 2 <;> ring
  have href : Ioo (t - r ^ 2 * (3 / 2)) t ×ˢ
      horizontalBall (G.horizontalFields hq) x (r * (5 / 4)) =
        harnackLaterIterationCylinder x t r 1 := by
    simpa only [one_pow, mul_one] using hset 1
  rw [hset ρ, hset R, href] at hv
  let μ : Measure (ℝ × CarnotPoint G hq hqpos hspan) := volume.prod (CarnotPoint.volume G hq hqpos hspan)
  have hsub (σ : ℝ) (hσ0 : 0 ≤ σ) (hσ : σ ≤ 1) :
      harnackLaterIterationCylinder x t r σ ⊆
        Ioo (t - 4 * r ^ 2) t ×ˢ Metric.ball x (2 * r) := by
    intro z hz
    refine ⟨⟨?_, hz.1.2⟩, ?_⟩
    · have hsq : σ ^ 2 ≤ 1 := by nlinarith
      have htime : t - 4 * r ^ 2 ≤ t - 3 / 2 * σ ^ 2 * r ^ 2 := by
        nlinarith [mul_le_mul_of_nonneg_right hsq (sq_nonneg r)]
      exact htime.trans_lt hz.1.1
    · exact Metric.ball_subset_ball (show 5 / 4 * σ * r ≤ 2 * r by
        nlinarith [mul_le_mul_of_nonneg_right hσ hr.le]) hz.2
  have hρ0 : 0 ≤ ρ := by linarith
  have hR0 : 0 ≤ R := by linarith
  have hρone : ρ ≤ 1 := hρR.le.trans hR
  have heq (σ : ℝ) (hσ0 : 0 ≤ σ) (hσ : σ ≤ 1) :
      (fun z => (v z + c)⁻¹) =ᵐ[μ.restrict (harnackLaterIterationCylinder x t r σ)]
        (fun z => (u z + c)⁻¹) := by
    filter_upwards [ae_restrict_of_ae_restrict_of_subset (hsub σ hσ0 hσ) hu0] with z hz
    simp only [v, max_eq_left hz]
  change eLpNormEssSup (fun z => (v z + c)⁻¹)
      (μ.restrict (harnackLaterIterationCylinder x t r ρ)) ≤
    ENNReal.ofReal ((C / (R - ρ) ^ (ν + 2)) ^ (1 / p)) *
      eLpNorm (fun z => (v z + c)⁻¹) (ENNReal.ofReal p)
        ((μ (harnackLaterIterationCylinder x t r 1))⁻¹ •
          μ.restrict (harnackLaterIterationCylinder x t r R)) at hv
  rw [eLpNormEssSup_congr_ae (heq ρ hρ0 hρone),
    eLpNorm_congr_ae (Measure.ae_smul_measure (heq R hR0 hR) _)] at hv
  exact reciprocal_normalized_norm_bound_to_moment μ _ _ hum hc hp (by linarith : 0 ≤ C)
    (sub_pos.mpr hρR)
    (ae_restrict_of_ae_restrict_of_subset (hsub ρ hρ0 hρone) hu0)
    (ae_restrict_of_ae_restrict_of_subset (hsub R hR0 hR) hu0) hv

/-- Uniformly elliptic matrix weak solutions satisfy the reciprocal mean-value
family on later Harnack cylinders, with open top time and the full reference
cylinder normalization. The constants precede the cylinder and perturbation. -/
theorem exists_uniform_matrix_harnackLater_reciprocal_mean_value_family
    {N q : ℕ} (G : HomogeneousGroup N) (hq : q ≤ N) (hqpos : 0 < q)
    (hspan : bracketSpansOn univ (G.horizontalFields hq))
    (hw : ∀ i : Fin q, G.weight (Fin.castLE hq i) = 1)
    (ell upper : ℝ) (hell : 0 < ell) (hupper : 0 ≤ upper) :
    ∀ p₀ : ℝ, 0 < p₀ →
      ∃ Cplus κplus : ℝ, 1 ≤ Cplus ∧ 0 ≤ κplus ∧
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
      ∀ σ' σ'' : ℝ, 9 / 10 ≤ σ' → σ' < σ'' → σ'' ≤ 1 →
      ∀ p : ℝ, 0 < p → p ≤ p₀ / 2 →
      let μ : Measure (ℝ × CarnotPoint G hq hqpos hspan) := volume.prod (CarnotPoint.volume G hq hqpos hspan)
      essSup (fun y => ENNReal.ofReal (1 / (u y + ε)))
        (μ.restrict (harnackLaterIterationCylinder x t r σ')) ≤
        (ENNReal.ofReal (Cplus * (1 / (σ'' - σ')) ^ κplus) *
          (μ (harnackLaterIterationCylinder x t r 1))⁻¹ *
            (∫⁻ y in harnackLaterIterationCylinder x t r σ'',
              ENNReal.ofReal (1 / (u y + ε)) ^ p ∂μ)) ^ (1 / p) := by
  obtain ⟨Cplus, κplus, hCplus, hκplus, hmean⟩ :=
    exists_uniform_matrix_harnackLater_reciprocal_mean_value
      G hq hqpos hspan hw ell upper hell hupper
  intro p₀ _hp₀
  refine ⟨Cplus, κplus, hCplus, hκplus, ?_⟩
  intro x t r hr coeff u hum hu0 hu ha hbound ε hε σ' σ'' hσ' hσ hσ'' p hp _hpp₀
  exact hmean x t r hr coeff u hum hu0 hu ha hbound ε hε σ' σ'' hσ' hσ hσ'' p hp

end HeatKernel
