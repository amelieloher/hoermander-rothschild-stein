-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.G4.ActualShortBallBox
public import RothschildStein.G4.ActualWeightedChartVolume
public import RothschildStein.G4.FrameChartVolumePolynomial
public import RothschildStein.G4.FrameVolumeAdapters

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set MeasureTheory Metric
open scoped BigOperators ENNReal
namespace RothschildStein.G4

/-- Actual auxiliary-ball volume bounds for one smooth system,
uniform over the compact center patch (BB Theorem 9.12, pp. 405–406).
The upper chart uses r/b with its own original Jacobian domain. -/
theorem exists_actual_auxiliary_ball_volume_bounds (k n s h q : ℕ)
    (hn : 0 < n) (hs : 0 < s) (horder : q + 1 = n * s + s) (hq : q + 1 ≤ h)
    (w : Fin (k + 1) → ℕ+) {M Δ R : ℝ}
    (hM : 0 ≤ M) (hΔ : 0 < Δ) (hR : 0 < R)
    (Ω : Set (Fin n → ℝ)) (hΩ : IsOpen Ω)
    (X : Fin (k + 1) → (Fin n → ℝ) → (Fin n → ℝ))
    (hX : ∀ j, ContDiffOn ℝ (⊤ : ℕ∞) (X j) Ω) (hstep : bracketStepOn Ω w X s)
    (x₀ : Fin n → ℝ) (hRΩ : closedBall x₀ R ⊆ Ω)
    (hjets : ∀ j, HasJetBound Ω (closedBall x₀ R) (X j)
      (max (2 * (n * s) + 2 * s) (max ((q + 1) * s) (h + 1 + s))) M)
    (hmax : ∀ y ∈ closedBall x₀ R, ∃ B : Fin n → ShortWord w s,
      Δ ≤ |frameDet (shortField w X) B y|) :
    ∃ c C ε : ℝ, 0 < c ∧ 0 < C ∧ 0 < ε ∧
      ∀ x ∈ closedBall x₀ (R / 16), ∀ r, 0 < r → r ≤ ε →
        let Λ := volumePolynomial (fun B : Fin n → ShortWord w s => frameDet (shortField w X) B x)
          (fun B => ∑ i, (shortWeight w (B i) : ℕ)) r
        ENNReal.ofReal (c * Λ) ≤
          volume {y | auxiliaryDistance (s := s) Ω w X x y < ENNReal.ofReal r} ∧
        volume {y | auxiliaryDistance (s := s) Ω w X x y < ENNReal.ofReal r} ≤
          ENNReal.ofReal (C * Λ) := by
  classical
  obtain ⟨a, b, r₀, D, κ, ha, ha1, hb, hba, hb1, hr₀, hr1, hD, hκ, hnκ, Φ, hcharts⟩ :=
    exists_actual_short_ball_box k n s h q hn hs horder hq w hM hΔ hR
      (show (0 : ℝ) < 1 / 2 by norm_num) (show (1 / 2 : ℝ) < 1 by norm_num)
      Ω hΩ X hX hstep x₀ hRΩ hjets hmax
  let weights : (Fin n → ShortWord w s) → Fin n → ℕ+ := fun B => shortWeight w ∘ B
  have hw : ∀ B, (∑ i, (weights B i : ℕ)) ≤ n * s := by
    intro B
    exact frame_natural_weight_le (shortWeight w)
      (fun I => ((mem_shortWordFamily_iff w I.val).mp I.property).2) B
  have hbb : b ≤ 1 := by linarith
  have hcard : (0 : ℝ) < Fintype.card (Fin n → ShortWord w s) := by
    obtain ⟨B, _⟩ := hmax x₀ (by simp [hR.le])
    exact_mod_cast Fintype.card_pos_iff.mpr ⟨B⟩
  let c : ℝ := ((2 : ℝ) ^ n / 4) * a ^ (n * s) / Fintype.card (Fin n → ShortWord w s)
  let C : ℝ := (4 * (2 : ℝ) ^ n) * (1 / b) ^ (n * s)
  have hc : 0 < c := by dsimp [c]; positivity
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨c, C, b * r₀, hc, hC, mul_pos hb hr₀, ?_⟩
  intro x hx r hr hrr
  have hxr : x ∈ closedBall x₀ R :=
    (closedBall_subset_closedBall (by linarith : R / 16 ≤ R)) hx
  have hspan : ∃ B : Fin n → ShortWord w s, frameDet (shortField w X) B x ≠ 0 := by
    obtain ⟨B, hB⟩ := hmax x hxr
    exact ⟨B, abs_pos.mp (hΔ.trans_le hB)⟩
  have hprovider : ∀ ρ, 0 < ρ → ρ ≤ r₀ →
      ∃ B : Fin n → ShortWord w s,
        (∀ A, |frameDet (shortField w X) A x| * ρ ^ (∑ i, (weights A i : ℕ)) ≤
          |frameDet (shortField w X) B x| * ρ ^ (∑ i, (weights B i : ℕ))) ∧
        ∃ F : (Fin n → ℝ) → (Fin n → ℝ),
          ContDiffOn ℝ (⊤ : ℕ∞) F (weightedBox (weights B) (a * ρ)) ∧
          InjOn F (weightedBox (weights B) (a * ρ)) ∧
          (∀ u ∈ weightedBox (weights B) (a * ρ),
            |frameDet (shortField w X) B x| / 4 ≤
              |Matrix.det (coordinateDerivativeMatrix (fderiv ℝ F u))| ∧
            |Matrix.det (coordinateDerivativeMatrix (fderiv ℝ F u))| ≤
              4 * |frameDet (shortField w X) B x|) ∧
          {y | auxiliaryDistance (s := s) Ω w X x y < ENNReal.ofReal (b * ρ)} ⊆
            F '' weightedBox (weights B) (a * ρ) ∧
          F '' weightedBox (weights B) (a * ρ) ⊆
            {y | auxiliaryDistance (s := s) Ω w X x y < ENNReal.ofReal ρ} := by
    intro ρ hρ hρr
    obtain ⟨B, hB⟩ := exists_suboptimal_frame (shortField w X) (shortWeight w)
      (t := 1) le_rfl hρ hspan
    have hbest : ∀ A, |frameDet (shortField w X) A x| * ρ ^ (∑ i, (weights A i : ℕ)) ≤
        |frameDet (shortField w X) B x| * ρ ^ (∑ i, (weights B i : ℕ)) := by
      intro A
      simpa only [IsSuboptimal, frameWeight_eq_nat_sum, zpow_natCast, one_mul, weights,
        Function.comp_apply] using hB A
    have hhalf : IsSuboptimal (shortField w X) (shortWeight w) B x (1 / 2) ρ := by
      intro A
      exact (mul_le_of_le_one_left (mul_nonneg (abs_nonneg _) (zpow_nonneg hρ.le _))
        (by norm_num : (1 / 2 : ℝ) ≤ 1)).trans (by simpa only [one_mul] using hB A)
    have hzero : (0 : Fin (Fintype.card (ShortWord w s)) → ℝ) ∈
        weightedBox (fun j => shortWeight w (shortIndex w j)) (b * ρ) := by
      intro i
      simpa only [Pi.zero_apply, abs_zero] using pow_pos (mul_pos hb hρ)
        (shortWeight w (shortIndex w i) : ℕ)
    obtain ⟨hAB, _, _, hinj, hjac, hinner, _, _, houter, _⟩ :=
      hcharts x hx ρ hρ hρr B hhalf 0 hzero
    refine ⟨B, hbest, _, hAB.1, hinj, hjac, hinner, ?_⟩
    intro y hy
    have hy' := houter rfl hy
    exact lt_of_le_of_lt (auxiliaryDistance_le_constantShortDistance Ω w X x y)
      (hy'.trans_le (ENNReal.ofReal_le_ofReal
        (mul_le_of_le_one_left hρ.le ha1.le)))
  -- Use the explicit constants of the adapter, uniform in x.
  have hrr₀ : r ≤ r₀ := hrr.trans (mul_le_of_le_one_left hr₀.le hbb)
  obtain ⟨B, hbest, F, hF, hinj, hjac, _, hout⟩ := hprovider r hr hrr₀
  have hlo := (actual_weighted_chart_volume_bounds (weights B) (mul_pos ha hr) F hF hinj hjac).1
  have hs' := chart_box_scalar_lower_bound (fun B => frameDet (shortField w X) B x)
    (fun B => ∑ i, (weights B i : ℕ)) (n * s) hw B ha ha1.le hr.le
    (show 0 ≤ (2 : ℝ) ^ n / 4 by positivity) hbest
  constructor
  · calc
      _ ≤ ENNReal.ofReal (((2 : ℝ) ^ n / 4) * |frameDet (shortField w X) B x| *
          (a * r) ^ (∑ i, (weights B i : ℕ))) := ENNReal.ofReal_le_ofReal hs'
      _ = ENNReal.ofReal (|frameDet (shortField w X) B x| / 4) *
          ENNReal.ofReal ((2 : ℝ) ^ n * (a * r) ^ (∑ i, (weights B i : ℕ))) := by
        rw [← ENNReal.ofReal_mul (by positivity)]
        congr 1
        ring
      _ ≤ _ := hlo.trans (measure_mono hout)
  · have hrb := div_pos hr hb
    have hrbr₀ : r / b ≤ r₀ := (div_le_iff₀ hb).mpr (by simpa only [mul_comm] using hrr)
    obtain ⟨B', _, F', hF', hinj', hjac', hinner, _⟩ := hprovider (r / b) hrb hrbr₀
    have hup := (actual_weighted_chart_volume_bounds (weights B') (mul_pos ha hrb)
      F' hF' hinj' hjac').2
    have hs' := chart_box_scalar_upper_bound (fun B => frameDet (shortField w X) B x)
      (fun B => ∑ i, (weights B i : ℕ)) (n * s) hw B' ha.le ha1.le hb hbb hr.le
      (show 0 ≤ 4 * (2 : ℝ) ^ n by positivity)
    calc
      _ ≤ volume (F' '' weightedBox (weights B') (a * (r / b))) := by
        apply measure_mono
        simpa only [mul_div_cancel₀ r hb.ne'] using hinner
      _ ≤ _ := hup
      _ = ENNReal.ofReal ((4 * (2 : ℝ) ^ n) * |frameDet (shortField w X) B' x| *
          (a * (r / b)) ^ (∑ i, (weights B' i : ℕ))) := by
        rw [← ENNReal.ofReal_mul (by positivity)]
        congr 1
        ring
      _ ≤ _ := ENNReal.ofReal_le_ofReal hs'

end RothschildStein.G4
