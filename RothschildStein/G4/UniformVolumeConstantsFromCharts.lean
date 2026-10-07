-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.G4.ActualWeightedChartVolume
public import RothschildStein.G4.FrameChartVolumePolynomial

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set MeasureTheory
open scoped BigOperators ENNReal

namespace RothschildStein.G4

/-- Original-radius volume bounds from actual injective charts.
The upper chart is evaluated at r/b, including its Jacobian hypotheses
on that chart's own box (BB p. 405, radius ). -/
theorem exists_uniform_volume_constants_of_actual_weighted_charts
    {ι : Type*} [Fintype ι] {n : ℕ}
    (weights : ι → Fin n → ℕ+) (D : ℕ)
    (hw : ∀ B, (∑ i, (weights B i : ℕ)) ≤ D)
    {a b r₀ : ℝ} (ha : 0 < a) (ha1 : a ≤ 1)
    (hb : 0 < b) (hb1 : b ≤ 1) (hr₀ : 0 < r₀)
    : ∃ c C ε : ℝ, 0 < c ∧ 0 < C ∧ 0 < ε ∧
      ∀ (lam : ι → ℝ) (ball : ℝ → Set (Fin n → ℝ)),
      (∀ r, 0 < r → r ≤ r₀ →
      ∃ B : ι, (∀ C, |lam C| * r ^ (∑ i, (weights C i : ℕ)) ≤
          |lam B| * r ^ (∑ i, (weights B i : ℕ))) ∧
        ∃ F : (Fin n → ℝ) → (Fin n → ℝ),
          ContDiffOn ℝ (⊤ : ℕ∞) F (weightedBox (weights B) (a * r)) ∧
          InjOn F (weightedBox (weights B) (a * r)) ∧
          (∀ u ∈ weightedBox (weights B) (a * r),
            |lam B| / 4 ≤ |Matrix.det (coordinateDerivativeMatrix (fderiv ℝ F u))| ∧
            |Matrix.det (coordinateDerivativeMatrix (fderiv ℝ F u))| ≤ 4 * |lam B|) ∧
          ball (b * r) ⊆ F '' weightedBox (weights B) (a * r) ∧
          F '' weightedBox (weights B) (a * r) ⊆ ball r) →
      ∀ r, 0 < r → r ≤ ε →
        ENNReal.ofReal (c * volumePolynomial lam (fun B => ∑ i, (weights B i : ℕ)) r) ≤
          volume (ball r) ∧
        volume (ball r) ≤
          ENNReal.ofReal (C * volumePolynomial lam (fun B => ∑ i, (weights B i : ℕ)) r) := by
  classical
  let c : ℝ := ((2 : ℝ) ^ n / 4) * a ^ D / ((Fintype.card ι : ℝ)+1)
  let C : ℝ := (4 * (2 : ℝ) ^ n) * (1 / b) ^ D
  refine ⟨c,C,b*r₀,by dsimp [c]; positivity,
    by dsimp [C]; positivity,mul_pos hb hr₀,?_⟩
  intro lam ball hchart
  obtain ⟨B₀,_⟩ := hchart r₀ hr₀ le_rfl
  have hc : (0 : ℝ) < Fintype.card ι := by
    exact_mod_cast Fintype.card_pos_iff.mpr ⟨B₀⟩
  intro r hr hrr
  have hrr₀ : r ≤ r₀ := hrr.trans (mul_le_of_le_one_left hr₀.le hb1)
  obtain ⟨B, hmax, F, hF, hinj, hjac, _, hout⟩ := hchart r hr hrr₀
  have hlo := (actual_weighted_chart_volume_bounds (weights B) (mul_pos ha hr) F hF hinj hjac).1
  have hs := chart_box_scalar_lower_bound lam (fun B => ∑ i, (weights B i : ℕ)) D hw B
    ha ha1 hr.le (show 0 ≤ (2 : ℝ) ^ n / 4 by positivity) hmax
  have hs0 : c * volumePolynomial lam (fun B => ∑ i, (weights B i : ℕ)) r ≤
      (((2 : ℝ)^n/4)*a^D/(Fintype.card ι : ℝ)) *
        volumePolynomial lam (fun B => ∑ i, (weights B i : ℕ)) r := by
    apply mul_le_mul_of_nonneg_right _ (volumePolynomial_nonneg _ _ hr.le)
    exact div_le_div_of_nonneg_left (by positivity) hc (by linarith)
  have hs' := hs0.trans hs
  have hnormalize : (|lam B| / 4) * ((2 : ℝ) ^ n * (a * r) ^ (∑ i, (weights B i : ℕ))) =
      ((2 : ℝ) ^ n / 4) * |lam B| * (a * r) ^ (∑ i, (weights B i : ℕ)) := by ring
  constructor
  · calc
      _ ≤ ENNReal.ofReal (((2 : ℝ) ^ n / 4) * |lam B| *
          (a * r) ^ (∑ i, (weights B i : ℕ))) := ENNReal.ofReal_le_ofReal hs'
      _ = ENNReal.ofReal (|lam B| / 4) *
          ENNReal.ofReal ((2 : ℝ) ^ n * (a * r) ^ (∑ i, (weights B i : ℕ))) := by
        rw [← ENNReal.ofReal_mul (by positivity), hnormalize]
      _ ≤ _ := hlo.trans (measure_mono hout)
  · have hrb : 0 < r / b := div_pos hr hb
    have hrbr₀ : r / b ≤ r₀ := (div_le_iff₀ hb).mpr (by simpa only [mul_comm] using hrr)
    obtain ⟨B', _, F', hF', hinj', hjac', hinner, _⟩ := hchart (r / b) hrb hrbr₀
    have hup := (actual_weighted_chart_volume_bounds (weights B') (mul_pos ha hrb)
      F' hF' hinj' hjac').2
    have hs' := chart_box_scalar_upper_bound lam (fun B => ∑ i, (weights B i : ℕ)) D hw B'
      ha.le ha1 hb hb1 hr.le (show 0 ≤ 4 * (2 : ℝ) ^ n by positivity)
    have hnormalize' : (4 * |lam B'|) * ((2 : ℝ) ^ n *
        (a * (r / b)) ^ (∑ i, (weights B' i : ℕ))) =
        (4 * (2 : ℝ) ^ n) * |lam B'| * (a * (r / b)) ^ (∑ i, (weights B' i : ℕ)) := by ring
    calc
      _ ≤ volume (F' '' weightedBox (weights B') (a * (r / b))) := by
        apply measure_mono
        simpa only [mul_div_cancel₀ r hb.ne'] using hinner
      _ ≤ _ := hup
      _ = ENNReal.ofReal ((4 * (2 : ℝ) ^ n) * |lam B'| *
          (a * (r / b)) ^ (∑ i, (weights B' i : ℕ))) := by
        rw [← ENNReal.ofReal_mul (by positivity), hnormalize']
      _ ≤ _ := ENNReal.ofReal_le_ofReal hs'

end RothschildStein.G4
