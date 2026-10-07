-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.G4.ConvexChartContraction
public import RothschildStein.G4.ControlledChartSegments
public import RothschildStein.G4.ControlledLiftFromSmallStart

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set Function

namespace RothschildStein.G4

/-- Actual analytic estimates supply all vertical lifts in the
injectivity transfer. Only the old-chart inverse and image containment
remain as geometric inputs (BB Prop 9.55, pp. 456–458). -/
theorem exists_uniform_analytic_chart_transfer {m n s : ℕ}
    {a D : ℝ} (ha : 0 < a) (ha1 : a ≤ 1) (hD : 0 ≤ D) :
    ∃ b : ℝ, 0 < b ∧ b < a / 8 ∧ 2 * b ≤ 1 ∧
      ∀ (w : Fin m → ℕ+) (A B : Fin n → Fin m), Injective A →
        (∀ i, (w (A i) : ℕ) ≤ s) → (∀ i, (w (B i) : ℕ) ≤ s) →
      ∀ (Z : Fin m → (Fin n → ℝ) → (Fin n → ℝ)) (Ω : Set (Fin n → ℝ)),
        (∀ J, ContinuousOn (Z J) Ω) →
      ∀ (F G Ψ : (Fin n → ℝ) → (Fin n → ℝ)) (r κ β c : ℝ),
        0 < r → r ≤ 1 → 0 ≤ κ → (n : ℝ) * κ ≤ 1 / 4 →
        0 < β → β ≤ 1 → 3 * β ≤ (2 * b) ^ s → 0 ≤ c → c ≤ a / 4 →
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
        ContDiffOn ℝ (⊤ : ℕ∞) G (weightedBox (w ∘ A) (β * r)) →
        MapsTo G (weightedBox (w ∘ A) (β * r)) Ω →
        (∀ u ∈ weightedBox (w ∘ A) (β * r), frameDet Z A (G u) ≠ 0) →
        (∀ u ∈ weightedBox (w ∘ A) (β * r), ∀ j i,
          |frameCoefficient Z A (fun z => fderiv ℝ G u (Pi.single i 1) - Z (A i) z)
            j (G u)| ≤ κ * r ^ (((w (A j) : ℕ) : ℤ) - ((w (A i) : ℕ) : ℤ))) →
        ContinuousOn Ψ (F '' weightedBox (w ∘ B) (c * r)) →
        (∀ u ∈ weightedBox (w ∘ B) (c * r),
          Ψ (F u) ∈ weightedBox (w ∘ A) (β * r) ∧ G (Ψ (F u)) = F u) →
        InjOn F (weightedBox (w ∘ B) (c * r)) := by
  obtain ⟨b, hb, hba, hb1, hlift⟩ :=
    exists_uniform_controlled_lift_from_small_start (m := m) (n := n) (s := s) ha ha1 hD
  refine ⟨b, hb, hba, hb1, ?_⟩
  intro w A B hA hwA hwB Z Ω hZ F G Ψ r κ β c hr hr1 hκ hsmall hβ hβ1 hmargin
    hc hca hF hjac hdet herror hframe hG hmap hAdet hAerror hΨ hinverse
  have hquarter : weightedBox (w ∘ B) (c * r) ⊆ weightedBox (w ∘ B) (a / 4 * r) := by
    intro u hu i
    exact (hu i).trans_le (pow_le_pow_left₀ (mul_nonneg hc hr.le)
      (mul_le_mul_of_nonneg_right hca hr.le) _)
  have hSQ : weightedBox (w ∘ B) (c * r) ⊆ weightedBox (w ∘ B) (a * r) := by
    intro u hu i
    exact (hquarter hu i).trans_le (pow_le_pow_left₀ (by positivity)
      (by nlinarith : a / 4 * r ≤ a * r) _)
  apply injOn_of_convex_chart_contraction_lifts (convex_weightedBox _ _) hSQ
    (isOpen_weightedBox _ _) (convex_weightedBox _ _) F G Ψ hF hjac hG.continuousOn hΨ hinverse
  intro z hz z' hz' u hu hstart
  have hcurve := chart_segment_isControlledCurve w A hA hwA Z hZ G hβ hβ1 hr hκ
    hsmall (mul_pos (by norm_num) hb) hb1 hmargin hG hmap hAdet hAerror hz hz'
  obtain ⟨θ, hcont, hinit, hrange, hproj, _hAC⟩ :=
    hlift w B hwB Z F r κ hr hr1 hκ hsmall hF hjac hdet herror hframe u
      (hquarter hu) Ω _ hcurve (by simpa only [zero_smul, add_zero] using hstart)
  exact ⟨θ, hcont, hinit, hrange, hproj⟩

end RothschildStein.G4
