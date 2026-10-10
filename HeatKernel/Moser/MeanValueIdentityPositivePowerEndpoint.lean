-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Moser.MeanValueIdentityPositivePowers
public import HeatKernel.Moser.MeanValueKernelNormFactors
import Mathlib.Tactic

/-! # Normalized positive-power mean values on Gaussian endpoint cylinders -/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set MeasureTheory TopologicalSpace RothschildStein
open scoped ENNReal
namespace HeatKernel
set_option backward.isDefEq.respectTransparency false

/-- The identity weak equation gives the normalized essential positive-power mean-value
estimate on the whole inner endpoint cylinder, including its open top time.
Continuity and preliminary local boundedness are unnecessary. -/
theorem exists_uniform_identity_kernel_endpoint_positive_power_mean_value {N q : ℕ}
    (G : HomogeneousGroup N) (hq : q ≤ N) (hqpos : 0 < q)
    (hspan : bracketSpansOn univ (G.horizontalFields hq))
    (hw : ∀ i : Fin q, G.weight (Fin.castLE hq i) = 1)
    {p : ℝ} (hp : 0 < p) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (s r : ℝ) (w : CarnotPoint G hq hqpos hspan),
      0 < r → 0 < s - 7 * r ^ 2 / 2 →
      ∀ v : ℝ × (Fin N → ℝ) → ℝ,
      (∀ σ > 0, ∀ z, 0 ≤ v (σ, z)) →
      IsLocalWeakSolution G hq hqpos hw hspan
        (fun _ _ i j => if i = j then 1 else 0)
        ⟨Ioo (s - 7 * r ^ 2 / 2) (s + r ^ 2 / 2), isOpen_Ioo⟩
        ⟨interior (horizontalBall (G.horizontalFields hq) w (2 * r)), isOpen_interior⟩
        (fun σ z => v (σ, z)) →
      eLpNormEssSup v (((volume : Measure ℝ).prod
        (CarnotPoint.volume G hq hqpos hspan)).restrict
          (Ioo (s - r ^ 2 / 2) (s + r ^ 2 / 2) ×ˢ Metric.ball w r)) ≤
        ENNReal.ofReal C * eLpNorm v (ENNReal.ofReal p)
          (ENNReal.ofReal (r ^ 2 *
            (CarnotPoint.volume G hq hqpos hspan).real (Metric.ball w (2 * r)))⁻¹ •
              ((volume.restrict (Ioo (s - 7 * r ^ 2 / 2) (s + r ^ 2 / 2))).prod
                ((CarnotPoint.volume G hq hqpos hspan).restrict (Metric.ball w (2 * r))))) := by
  let ν := max 2 (G.homogeneousDimension : ℝ) + 1
  obtain ⟨C, hC, hcylinder⟩ := exists_uniform_identity_cylinder_positive_power_bound
    G hq hqpos hspan hw (ν := ν) (by dsimp only [ν]; linarith) hp
  let b := (volume : Measure (Fin N → ℝ)).real (horizontalBall (G.horizontalFields hq) 0 1)
  have hb : 0 < b := ENNReal.toReal_pos
    (volume_horizontalBall_pos G hq hqpos hspan 0 (by norm_num)).ne'
    (volume_horizontalBall_lt_top G hq hqpos hspan hw 0 (by norm_num)).ne
  refine ⟨C * (b + 1) ^ (2 / p),
    mul_pos hC (Real.rpow_pos_of_pos (by linarith : 0 < b + 1) _), ?_⟩
  intro s r w hr hstart v hv0 hweak
  have h2r : 0 < 2 * r := by positivity
  let t₀ := s + r ^ 2 / 2
  have htime : t₀ - (2 * r) ^ 2 = s - 7 * r ^ 2 / 2 := by dsimp only [t₀]; ring
  have hballOpen := (isOpen_horizontalBall G hq hqpos hspan w (2 * r)).interior_eq
  have hsource : IsLocalWeakSolution G hq hqpos hw hspan
      (fun _ _ i j => if i = j then 1 else 0)
      ⟨Ioo (t₀ - (2 * r) ^ 2) t₀, isOpen_Ioo⟩
      ⟨horizontalBall (G.horizontalFields hq) w (2 * r),
        isOpen_horizontalBall G hq hqpos hspan w (2 * r)⟩ (fun σ z => v (σ, z)) := by
    simpa only [htime, t₀, hballOpen] using hweak
  have hpositive (σ : ℝ) (hσ : σ ∈ Ioo (t₀ - (2 * r) ^ 2) t₀) : 0 < σ := by
    rw [htime] at hσ
    exact hstart.trans hσ.1
  have hbound := hcylinder t₀ w (2 * r) h2r v
    (fun σ hσ z => hv0 σ (hpositive σ hσ) z) hsource
  let Sin := Ioo (s - r ^ 2 / 2) (s + r ^ 2 / 2) ×ˢ horizontalBall (G.horizontalFields hq) w r
  let Sout := Ioo (s - 7 * r ^ 2 / 2) (s + r ^ 2 / 2) ×ˢ
    horizontalBall (G.horizontalFields hq) w (2 * r)
  have hsub : Sin ⊆ Ioo (t₀ - (2 * r) ^ 2 / 2) t₀ ×ˢ
      horizontalBall (G.horizontalFields hq) w ((2 * r) / 2) := by
    intro z hz
    refine ⟨⟨?_, hz.1.2⟩, ?_⟩
    · dsimp only [t₀]
      nlinarith [hz.1.1, sq_nonneg r]
    · simpa only [show (2 * r) / 2 = r by ring] using hz.2
  have hsmall := (eLpNormEssSup_mono_measure v
    (Measure.absolutelyContinuous_of_le (Measure.restrict_mono hsub le_rfl))).trans hbound
  rw [htime] at hsmall
  change eLpNormEssSup v (volume.restrict Sin) ≤
    ENNReal.ofReal C * (ENNReal.ofReal (((2 * r) ^ (G.homogeneousDimension + 2))⁻¹) ^ (1 / p) *
      eLpNorm v (ENNReal.ofReal p) (volume.restrict Sout)) at hsmall
  have hBall (ρ : ℝ) :
      (@Metric.ball (CarnotPoint G hq hqpos hspan) _ w ρ : Set (Fin N → ℝ)) =
        horizontalBall (G.horizontalFields hq) w ρ :=
    CarnotPoint.coordinateBall_eq_horizontalBall G hq hqpos hspan w ρ
  have hvol : (CarnotPoint.volume G hq hqpos hspan).real (Metric.ball w (2 * r)) =
      (2 * r) ^ G.homogeneousDimension * b := by
    change (volume : Measure (Fin N → ℝ)).real
      (@Metric.ball (CarnotPoint G hq hqpos hspan) _ w (2 * r) : Set (Fin N → ℝ)) = _
    rw [hBall]
    exact real_volume_horizontalBall G hq hw w (2 * r) h2r
  rw [hvol]
  change eLpNormEssSup v (((volume : Measure ℝ).prod (volume : Measure (Fin N → ℝ))).restrict
      (Ioo (s - r ^ 2 / 2) (s + r ^ 2 / 2) ×ˢ
        (@Metric.ball (CarnotPoint G hq hqpos hspan) _ w r : Set (Fin N → ℝ)))) ≤
    ENNReal.ofReal (C * (b + 1) ^ (2 / p)) * eLpNorm v (ENNReal.ofReal p)
      (ENNReal.ofReal (r ^ 2 * ((2 * r) ^ G.homogeneousDimension * b))⁻¹ •
        ((volume.restrict (Ioo (s - 7 * r ^ 2 / 2) (s + r ^ 2 / 2))).prod
          ((volume : Measure (Fin N → ℝ)).restrict
            (@Metric.ball (CarnotPoint G hq hqpos hspan) _ w (2 * r)))))
  simp only [hBall, Measure.prod_restrict, ← Measure.volume_eq_prod]
  let D := r ^ 2 * ((2 * r) ^ G.homogeneousDimension * b)
  have hD : 0 < D := by dsimp only [D]; positivity
  change eLpNormEssSup v (volume.restrict Sin) ≤ ENNReal.ofReal (C * (b + 1) ^ (2 / p)) *
    eLpNorm v (ENNReal.ofReal p) (ENNReal.ofReal D⁻¹ • volume.restrict Sout)
  rw [ENNReal.ofReal_inv_of_pos hD]
  have hn : eLpNorm v (ENNReal.ofReal p) ((ENNReal.ofReal D)⁻¹ • volume.restrict Sout) =
      (ENNReal.ofReal D)⁻¹ ^ (1 / p) * eLpNorm v (ENNReal.ofReal p) (volume.restrict Sout) := by
    rw [eLpNorm_smul_measure_of_ne_zero_of_ne_top
      (ENNReal.ofReal_pos.mpr hp).ne' ENNReal.ofReal_ne_top]
    simp only [ENNReal.toReal_inv, ENNReal.toReal_ofReal hp.le, one_div, smul_eq_mul]
  rw [hn, ENNReal.ofReal_mul hC.le]
  have hfactor := identity_kernel_endpoint_positive_power_norm_factor_le G.homogeneousDimension hp hr hb
  exact hsmall.trans (by
    simpa only [mul_assoc] using
      mul_le_mul' (le_refl (ENNReal.ofReal C))
        (mul_le_mul' hfactor (le_refl (eLpNorm v (ENNReal.ofReal p) (volume.restrict Sout)))))

end HeatKernel
