-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Poincare.CurvePower
public import HeatKernel.Poincare.TranslatedCurve
public import HeatKernel.Poincare.TranslationEnergy
public import HeatKernel.Geometry.SmoothBallCutoff

/-! Uniform integral bounds for translation increments along horizontal paths. -/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set MeasureTheory RothschildStein
open scoped ENNReal BigOperators

namespace HeatKernel

/-- A single unit-speed translated horizontal path controls endpoint oscillation. -/
theorem ofReal_translation_increment_le_path_energy {N q : ℕ}
    (G : HomogeneousGroup N) (hq : q ≤ N) (x : Fin N → ℝ)
    {r p ℓ : ℝ} (hr : 0 < r) (hp : 1 ≤ p) (hℓ : 0 < ℓ) (hlength : ℓ < 3 * r)
    (u : (Fin N → ℝ) → ℝ)
    (hu : ∀ w ∈ horizontalBall (G.horizontalFields hq) x (4 * r), ContDiffAt ℝ 1 u w)
    (F : (Fin N → ℝ) → ℝ≥0∞)
    (henergy : ∀ w ∈ horizontalBall (G.horizontalFields hq) x (4 * r),
      F w = ENNReal.ofReal ((horizontalGradientNorm (G.horizontalFields hq) u w) ^ p))
    (z : Fin N → ℝ) (γ : ℝ → (Fin N → ℝ)) (a : Fin q → ℝ → ℝ)
    (hzero : γ 0 = 0) (hend : γ ℓ = z)
    (hγ : IsHorizontalCurveOn (G.horizontalFields hq) γ a 0 ℓ)
    (ha : ∀ t, controlNorm a t ≤ 1) (y : Fin N → ℝ)
    (hy : y ∈ horizontalBall (G.horizontalFields hq) x r) :
    ENNReal.ofReal (|u (G.mul y z) - u y| ^ p) ≤
      ENNReal.ofReal (ℓ ^ (p - 1)) * ∫⁻ t in Icc (0 : ℝ) ℓ, F (G.mul y (γ t)) := by
  have hp0 : 0 ≤ p := le_trans zero_le_one hp
  let C := ENNReal.ofReal (ℓ ^ (p - 1))
  have himage : ∀ y ∈ horizontalBall (G.horizontalFields hq) x r,
      (fun t => G.mul y (γ t)) '' uIcc 0 ℓ ⊆ horizontalBall (G.horizontalFields hq) x (4 * r) :=
    fun y hy => translated_horizontalCurve_image_subset_four_ball G hq hγ hℓ.le hr hlength hzero ha hy
  have hc := hγ.leftTranslation G hq y
  have huc : ∀ w ∈ (fun t => G.mul y (γ t)) '' uIcc 0 ℓ, ContDiffAt ℝ 1 u w :=
    fun w hw => hu w (himage y hy hw)
  have hX := fun i => (G.horizontalFields_contDiff hq i).continuous
  have hb := hc.abs_sub_rpow_le_integral_horizontalGradient_rpow hℓ hX huc
    (Filter.Eventually.of_forall ha) hp
  simp only [hzero, hend, G2.mul_zero, sub_zero] at hb
  have hi := hc.integrableOn_horizontalGradient_rpow hX huc hp0
  have he : ENNReal.ofReal (∫ t in Icc (0 : ℝ) ℓ,
      (horizontalGradientNorm (G.horizontalFields hq) u (G.mul y (γ t))) ^ p) =
      ∫⁻ t in Icc (0 : ℝ) ℓ, F (G.mul y (γ t)) := by
    change IntegrableOn (fun t => (horizontalGradientNorm (G.horizontalFields hq) u (G.mul y (γ t))) ^ p) (Icc 0 ℓ) at hi
    rw [ofReal_integral_eq_lintegral_ofReal hi
      (Filter.Eventually.of_forall fun t => Real.rpow_nonneg (Real.sqrt_nonneg _) _)]
    apply lintegral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
    exact (henergy _ (himage y hy ⟨t, by simpa only [uIcc_of_le hℓ.le] using ht, rfl⟩)).symm
  change |u (G.mul y z) - u y| ^ p ≤ ℓ ^ (p - 1) *
    ∫ t in Icc (0 : ℝ) ℓ, (horizontalGradientNorm (G.horizontalFields hq) u (G.mul y (γ t))) ^ p at hb
  have hb' := ENNReal.ofReal_le_ofReal hb
  rw [ENNReal.ofReal_mul (Real.rpow_nonneg hℓ.le (p - 1))] at hb'
  change ENNReal.ofReal (|u (G.mul y z) - u y| ^ p) ≤ C * _ at hb'
  rw [he] at hb'
  exact hb'

/-- Haar invariance bounds the total energy of a translated horizontal path. -/
theorem lintegral_horizontal_path_energy_le {N q : ℕ}
    (G : HomogeneousGroup N) (hq : q ≤ N) (x : Fin N → ℝ)
    {r ℓ : ℝ} (hr : 0 < r) (hℓ : 0 < ℓ) (hlength : ℓ < 3 * r)
    (γ : ℝ → (Fin N → ℝ)) (a : Fin q → ℝ → ℝ)
    (hzero : γ 0 = 0) (hγ : IsHorizontalCurveOn (G.horizontalFields hq) γ a 0 ℓ)
    (ha : ∀ t, controlNorm a t ≤ 1)
    (F : (Fin N → ℝ) → ℝ≥0∞) (hF : Measurable F) :
    (∫⁻ y in horizontalBall (G.horizontalFields hq) x r,
      ∫⁻ t in Icc (0 : ℝ) ℓ, F (G.mul y (γ t))) ≤
      volume (Icc (0 : ℝ) ℓ) * ∫⁻ w in horizontalBall (G.horizontalFields hq) x (4 * r), F w := by
  let B := horizontalBall (G.horizontalFields hq) x r
  let U := horizontalBall (G.horizontalFields hq) x (4 * r)
  have hγmeas : AEMeasurable γ (volume.restrict (Icc (0 : ℝ) ℓ)) :=
    (hγ.absolutelyContinuous.continuousOn.mono Icc_subset_uIcc).aemeasurable measurableSet_Icc
  have hmeas : AEMeasurable (fun p : (Fin N → ℝ) × ℝ => F (G.mul p.1 (γ p.2)))
      ((volume.restrict B).prod (volume.restrict (Icc (0 : ℝ) ℓ))) :=
    aemeasurable_mul_curve G hγmeas hF
  have hsub : ∀ t ∈ Icc (0 : ℝ) ℓ, (fun y => G.mul y (γ t)) '' B ⊆ U := by
    rintro t ht w ⟨y, hy, rfl⟩
    exact translated_horizontalCurve_image_subset_four_ball G hq hγ hℓ.le hr hlength hzero ha hy
      ⟨t, by simpa only [uIcc_of_le hℓ.le] using ht, rfl⟩
  exact lintegral_translated_path_le G volume measurableSet_Icc γ F hmeas hsub

/-- Integrating a fixed translated horizontal path gives the uniform energy bound. -/
theorem lintegral_translation_increment_le_of_horizontalCurve {N q : ℕ}
    (G : HomogeneousGroup N) (hq : q ≤ N) (hqpos : 0 < q)
    (hspan : bracketSpansOn univ (G.horizontalFields hq))
    (x : Fin N → ℝ) {r p ℓ : ℝ} (hr : 0 < r) (hp : 1 ≤ p)
    (u : (Fin N → ℝ) → ℝ)
    (hu : ∀ w ∈ horizontalBall (G.horizontalFields hq) x (4 * r), ContDiffAt ℝ 1 u w)
    (F : (Fin N → ℝ) → ℝ≥0∞) (hF : Measurable F)
    (henergy : ∀ w ∈ horizontalBall (G.horizontalFields hq) x (4 * r),
      F w = ENNReal.ofReal ((horizontalGradientNorm (G.horizontalFields hq) u w) ^ p))
    (z : Fin N → ℝ) (γ : ℝ → (Fin N → ℝ)) (a : Fin q → ℝ → ℝ)
    (hℓ : 0 < ℓ) (hlength : ℓ < 3 * r) (hzero : γ 0 = 0) (hend : γ ℓ = z)
    (hγ : IsHorizontalCurveOn (G.horizontalFields hq) γ a 0 ℓ)
    (ha : ∀ t, controlNorm a t ≤ 1) :
    (∫⁻ y in horizontalBall (G.horizontalFields hq) x r,
      ENNReal.ofReal (|u (G.mul y z) - u y| ^ p)) ≤
      ENNReal.ofReal ((3 * r) ^ p) * ∫⁻ w in horizontalBall (G.horizontalFields hq) x (4 * r), F w := by
  have hp0 : 0 ≤ p := le_trans zero_le_one hp
  let B := horizontalBall (G.horizontalFields hq) x r
  let U := horizontalBall (G.horizontalFields hq) x (4 * r)
  let C := ENNReal.ofReal (ℓ ^ (p - 1))
  have hpoint : ∀ y ∈ B, ENNReal.ofReal (|u (G.mul y z) - u y| ^ p) ≤
      C * ∫⁻ t in Icc (0 : ℝ) ℓ, F (G.mul y (γ t)) :=
    fun y hy => ofReal_translation_increment_le_path_energy G hq x hr hp hℓ hlength
      u hu F henergy z γ a hzero hend hγ ha y hy
  have hpath := lintegral_horizontal_path_energy_le G hq x hr hℓ hlength γ a hzero hγ ha F hF
  have hpow : ℓ ^ (p - 1) * ℓ = ℓ ^ p := by
    calc
      ℓ ^ (p - 1) * ℓ = ℓ ^ (p - 1) * ℓ ^ (1 : ℝ) := by rw [Real.rpow_one]
      _ = ℓ ^ p := by rw [← Real.rpow_add hℓ, sub_add_cancel]
  calc
    (∫⁻ y in B, ENNReal.ofReal (|u (G.mul y z) - u y| ^ p)) ≤
        ∫⁻ y in B, C * (∫⁻ t in Icc (0 : ℝ) ℓ, F (G.mul y (γ t))) :=
      lintegral_mono_ae (ae_restrict_of_forall_mem
        (isOpen_horizontalBall G hq hqpos hspan x r).measurableSet hpoint)
    _ = C * ∫⁻ y in B, ∫⁻ t in Icc (0 : ℝ) ℓ, F (G.mul y (γ t)) :=
      lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ ≤ C * ((volume (Icc (0 : ℝ) ℓ)) * ∫⁻ w in U, F w) := mul_le_mul_right hpath C
    _ = ENNReal.ofReal (ℓ ^ p) * ∫⁻ w in U, F w := by
      simp only [Real.volume_Icc, sub_zero]
      rw [← mul_assoc, ← ENNReal.ofReal_mul (Real.rpow_nonneg hℓ.le (p - 1)), hpow]
    _ ≤ ENNReal.ofReal ((3 * r) ^ p) * ∫⁻ w in U, F w :=
      mul_le_mul_left (ENNReal.ofReal_le_ofReal (Real.rpow_le_rpow hℓ.le hlength.le hp0)) _


/-- A fixed increment in the doubled identity ball has a uniform oscillation bound over
the original ball. An explicit measurable energy extension agrees with the gradient energy
on the fourfold ball; the chosen path need not depend measurably on the increment. -/
theorem lintegral_translation_increment_le {N q : ℕ}
    (G : HomogeneousGroup N) (hq : q ≤ N) (hqpos : 0 < q)
    (hspan : bracketSpansOn univ (G.horizontalFields hq))
    (x : Fin N → ℝ) {r p : ℝ} (hr : 0 < r) (hp : 1 ≤ p)
    (u : (Fin N → ℝ) → ℝ)
    (hu : ∀ w ∈ horizontalBall (G.horizontalFields hq) x (4 * r), ContDiffAt ℝ 1 u w)
    (F : (Fin N → ℝ) → ℝ≥0∞) (hF : Measurable F)
    (henergy : ∀ w ∈ horizontalBall (G.horizontalFields hq) x (4 * r),
      F w = ENNReal.ofReal ((horizontalGradientNorm (G.horizontalFields hq) u w) ^ p))
    (z : Fin N → ℝ) (hz : z ∈ horizontalBall (G.horizontalFields hq) 0 (2 * r)) :
    (∫⁻ y in horizontalBall (G.horizontalFields hq) x r,
      ENNReal.ofReal (|u (G.mul y z) - u y| ^ p)) ≤
      ENNReal.ofReal ((3 * r) ^ p) * ∫⁻ w in horizontalBall (G.horizontalFields hq) x (4 * r), F w := by
  have hdist : horizontalL2Distance (G.horizontalFields hq) 0 z < ENNReal.ofReal (3 * r) :=
    (show horizontalL2Distance (G.horizontalFields hq) 0 z < ENNReal.ofReal (2 * r) from hz).trans
      ((ENNReal.ofReal_lt_ofReal_iff (by positivity)).2 (by linarith))
  obtain ⟨ℓ, γ, a, hℓ, hlength, hzero, hend, hγ, ha, _⟩ :=
    exists_horizontalCurve_lt_of_distance_lt hdist
  exact lintegral_translation_increment_le_of_horizontalCurve G hq hqpos hspan x hr hp
    u hu F hF henergy z γ a hℓ hlength hzero hend hγ ha

end HeatKernel
