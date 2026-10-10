-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Poincare.UniformTranslation
public import HeatKernel.Poincare.MeanPowerIntegral
public import HeatKernel.Poincare.PairwiseOscillation
public import HeatKernel.Poincare.TranslationAverage

/-! Weak horizontal Poincaré bounds with the explicit dilation and volume factor. -/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set MeasureTheory RothschildStein
open scoped ENNReal

namespace HeatKernel

/-- Weak Poincaré in nonnegative-integral form, with explicit local integrability and
measurable energy-extension inputs. The translation estimate and averaging comparison
are proved from horizontal paths and Haar invariance. -/
theorem lintegral_weak_horizontalPoincare_of_integrable {N q : ℕ}
    (G : HomogeneousGroup N) (hq : q ≤ N) (hqpos : 0 < q)
    (hspan : bracketSpansOn univ (G.horizontalFields hq))
    (hw : ∀ i : Fin q, G.weight (Fin.castLE hq i) = 1)
    (x : Fin N → ℝ) {r p : ℝ} (hr : 0 < r) (hp : 1 ≤ p)
    (u : (Fin N → ℝ) → ℝ) (humeas : Measurable u)
    (hu : ∀ w ∈ horizontalBall (G.horizontalFields hq) x (4 * r), ContDiffAt ℝ 1 u w)
    (hui : IntegrableOn u (horizontalBall (G.horizontalFields hq) x r))
    (hpairi : ∀ y, IntegrableOn (fun z => |u y - u z| ^ p)
      (horizontalBall (G.horizontalFields hq) x r))
    (F : (Fin N → ℝ) → ℝ≥0∞) (hF : Measurable F)
    (henergy : ∀ w ∈ horizontalBall (G.horizontalFields hq) x (4 * r),
      F w = ENNReal.ofReal ((horizontalGradientNorm (G.horizontalFields hq) u w) ^ p)) :
    (∫⁻ y in horizontalBall (G.horizontalFields hq) x r,
      ENNReal.ofReal (|u y - ⨍ z in horizontalBall (G.horizontalFields hq) x r, u z| ^ p)) ≤
      (2 : ℝ≥0∞) ^ G.homogeneousDimension * ENNReal.ofReal ((3 * r) ^ p) *
        ∫⁻ w in horizontalBall (G.horizontalFields hq) x (4 * r), F w := by
  let B := horizontalBall (G.horizontalFields hq) x r
  let S := horizontalBall (G.horizontalFields hq) 0 (2 * r)
  let U := horizontalBall (G.horizontalFields hq) x (4 * r)
  let pair := fun y z : Fin N → ℝ => ENNReal.ofReal (|u y - u z| ^ p)
  have hB0 : volume B ≠ 0 := (volume_horizontalBall_pos G hq hqpos hspan x hr).ne'
  have hBtop : volume B ≠ ⊤ := (volume_horizontalBall_lt_top G hq hqpos hspan hw x hr.le).ne
  have : Fact (volume B < ⊤) := ⟨lt_top_iff_ne_top.mpr hBtop⟩
  have : NeZero (volume.restrict B) := ⟨mt Measure.restrict_eq_zero.mp hB0⟩
  have hp0 : 0 ≤ p := le_trans zero_le_one hp
  have hpow : Measurable (fun t : ℝ => ENNReal.ofReal (|t| ^ p)) :=
    ENNReal.continuous_ofReal.measurable.comp
      ((Real.continuous_rpow_const hp0).measurable.comp measurable_id.abs)
  have hpairmeas : ∀ y, Measurable (pair y) := fun y =>
    hpow.comp (measurable_const.sub humeas)
  have htransmeas : Measurable (fun p : (Fin N → ℝ) × (Fin N → ℝ) =>
      pair p.1 (G.mul p.1 p.2)) :=
    hpow.comp ((humeas.comp measurable_fst).sub
      (humeas.comp (G2.continuous_mul G).measurable))
  have hj := lintegral_abs_sub_average_rpow_le_pairwise hp hui hpairi
  simp only [Measure.restrict_apply_univ] at hj
  have hchange := lintegral_pairwise_le_translation_pairs G hq hqpos hspan x hr.le hpairmeas htransmeas
  have haverage : (∫⁻ y in B, ENNReal.ofReal (|u y - ⨍ z in B, u z| ^ p)) ≤
      (volume B)⁻¹ * ∫⁻ z in S, ∫⁻ y in B, pair y (G.mul y z) :=
    hj.trans (mul_le_mul_right hchange _)
  have htranslation : ∀ᵐ z ∂volume.restrict S,
      (∫⁻ y in B, pair y (G.mul y z)) ≤
        ENNReal.ofReal ((3 * r) ^ p) * ∫⁻ w in U, F w := by
    apply ae_restrict_of_forall_mem (isOpen_horizontalBall G hq hqpos hspan 0 (2 * r)).measurableSet
    intro z hz
    simpa only [pair, abs_sub_comm] using
      lintegral_translation_increment_le G hq hqpos hspan x hr hp u hu F hF henergy z hz
  have hvolume : volume S ≤ (2 : ℝ≥0∞) ^ G.homogeneousDimension * volume B := by
    dsimp only [S, B]
    rw [volume_horizontalBall_double G hq hw 0 hr,
      volume_horizontalBall G hq hw 0 hr, volume_horizontalBall G hq hw x hr]
  have hh := lintegral_oscillation_le_of_translation_estimate hB0 hBtop haverage htranslation hvolume
  simpa only [mul_assoc] using hh

end HeatKernel
