-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.G4.ContinuousLiftVariation
public import RothschildStein.G4.WeightedChartPathLifting
public import RothschildStein.G4.WeightedVariationLipschitz

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set

namespace RothschildStein.G4

/-- The short-path radius is numerical and chosen before the
actual fields, chart and controlled path. Actual Jacobian, Cramer and
derivative-error bounds then give an absolutely continuous lift through
time 1 with strict half-box clearance (BB Prop 9.52, pp. 448–449). -/
theorem exists_uniform_controlled_chart_lift_radius {m n s : ℕ}
    {a D : ℝ} (ha : 0 < a) (ha1 : a ≤ 1) (hD : 0 ≤ D) :
    ∃ b : ℝ, 0 < b ∧ b < a / 4 ∧ 2 * b ≤ 1 ∧
      ∀ (w : Fin m → ℕ+) (B : Fin n → Fin m), (∀ i, (w (B i) : ℕ) ≤ s) →
      ∀ (Z : Fin m → (Fin n → ℝ) → (Fin n → ℝ))
        (F : (Fin n → ℝ) → (Fin n → ℝ)) (r κ : ℝ),
        0 < r → r ≤ 1 → 0 ≤ κ → (n : ℝ) * κ ≤ 1 / 4 →
        ContDiffOn ℝ (⊤ : ℕ∞) F (weightedBox (w ∘ B) (a * r)) →
        (∀ u ∈ weightedBox (w ∘ B) (a * r),
          Matrix.det (coordinateDerivativeMatrix (fderiv ℝ F u)) ≠ 0) →
        (∀ u ∈ weightedBox (w ∘ B) (a * r), frameDet Z B (F u) ≠ 0) →
        (∀ u ∈ weightedBox (w ∘ B) (a * r), ∀ i j, |frameCoefficient Z B
          (fun z => fderiv ℝ F u (Pi.single j 1) - Z (B j) z) i (F u)| ≤
            κ * r ^ (((w (B i) : ℕ) : ℤ) - ((w (B j) : ℕ) : ℤ))) →
        (∀ u ∈ weightedBox (w ∘ B) (a * r), ∀ J j,
          |frameCoefficient Z B (Z J) j (F u)| ≤
            D * r ^ (((w (B j) : ℕ) : ℤ) - ((w J : ℕ) : ℤ))) →
        ∀ (Ω : Set (Fin n → ℝ)) (γ : ℝ → (Fin n → ℝ)),
          isControlledCurve Ω w Z (2 * b * r) γ → F 0 = γ 0 →
          ∃ θ, IsChartPathLift F γ θ (weightedBox (w ∘ B) (a * r)) 1 ∧
            AbsolutelyContinuousOnInterval θ 0 1 ∧
            ∀ t ∈ Icc (0 : ℝ) 1, θ t ∈ weightedBox (w ∘ B) (a * r / 2) := by
  let C : ℝ := 2 * (m : ℝ) * n * D * (4 / 3 : ℝ)
  have hC : 0 ≤ C := by dsimp [C]; positivity
  obtain ⟨b, hb, hba, hb1, hmargin⟩ := exists_weighted_lift_margin s ha ha1 hC
  refine ⟨b, hb, hba, hb1, ?_⟩
  intro w B hw Z F r κ hr hr1 hκ hsmall hF hjac hdet herror hframe Ω γ hγ hstart
  have hCb : 0 ≤ C * b := mul_nonneg hC hb.le
  have hvar : ∀ T : ℝ, T ≤ 1 → ∀ θ : ℝ → (Fin n → ℝ),
      IsChartPathLift F γ θ (weightedBox (w ∘ B) (a * r)) T →
      ∀ σ ∈ Icc (0 : ℝ) T, ∀ τ ∈ Icc (0 : ℝ) T, ∀ i,
        |θ τ i - θ σ i| ≤ C * b * r ^ (w (B i) : ℕ) * |τ - σ| := by
    intro T hT θ hθ
    exact continuous_partialLift_weighted_variation Z w B (isOpen_weightedBox (w ∘ B) (a * r))
      F hF hjac hdet hr hκ hsmall hb.le hb1 hD herror hframe hγ hT θ
      hθ.1 hθ.2.2.1 hθ.2.2.2
  have hγcont : ContinuousOn γ (Icc (0 : ℝ) 1) := by
    simpa only [uIcc_of_le zero_le_one] using hγ.2.1.continuousOn
  obtain ⟨θ, hθ⟩ := exists_chartPathLift_of_weighted_variation (w ∘ B) hw ha ha1 hr hr1
    hCb hmargin F γ hF hjac hγcont hstart hvar
  have hbound := hvar 1 le_rfl θ hθ
  have hLip := weighted_variation_lipschitzOn (w ∘ B) hr hr1 hCb θ hbound
  refine ⟨θ, hθ, ?_, ?_⟩
  · exact (show LipschitzOnWith ⟨C * b, hCb⟩ θ (uIcc 0 1) by
      simpa only [uIcc_of_le zero_le_one] using hLip).absolutelyContinuousOnInterval
  · intro t ht
    apply weighted_lift_mem_halfBox (w ∘ B) hw ha ha1 hr hmargin (θ t)
    intro i
    have hh := hbound 0 ⟨le_rfl, zero_le_one⟩ t ht i
    rw [hθ.2.1, Pi.zero_apply, sub_zero, sub_zero, abs_of_nonneg ht.1] at hh
    exact hh.trans (mul_le_of_le_one_right (mul_nonneg hCb (pow_nonneg hr.le _)) ht.2)

end RothschildStein.G4
