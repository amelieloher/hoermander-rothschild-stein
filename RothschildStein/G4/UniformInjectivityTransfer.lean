-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.G4.AnalyticChartTransfer
public import RothschildStein.G4.InjectiveChartContinuousInverse

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set Function

namespace RothschildStein.G4

/-- Transfer injectivity from an actual old chart to an actual
new chart whose small image lies in the old image. The inverse and every
vertical lift are constructed, not assumed (BB Prop 9.55, pp. 456–458). -/
theorem exists_uniform_actual_chart_injectivity_transfer {m n s : ℕ}
    {a D : ℝ} (ha : 0 < a) (ha1 : a ≤ 1) (hD : 0 ≤ D) :
    ∃ b : ℝ, 0 < b ∧ b < a / 8 ∧ 2 * b ≤ 1 ∧
      ∀ (w : Fin m → ℕ+) (A B : Fin n → Fin m), Injective A →
        (∀ i, (w (A i) : ℕ) ≤ s) → (∀ i, (w (B i) : ℕ) ≤ s) →
      ∀ (Z : Fin m → (Fin n → ℝ) → (Fin n → ℝ)) (Ω : Set (Fin n → ℝ)),
        (∀ J, ContinuousOn (Z J) Ω) →
      ∀ (F G : (Fin n → ℝ) → (Fin n → ℝ)) (r κ β c : ℝ),
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
        (∀ u ∈ weightedBox (w ∘ A) (β * r),
          Matrix.det (coordinateDerivativeMatrix (fderiv ℝ G u)) ≠ 0) →
        InjOn G (weightedBox (w ∘ A) (β * r)) →
        F '' weightedBox (w ∘ B) (c * r) ⊆ G '' weightedBox (w ∘ A) (β * r) →
        InjOn F (weightedBox (w ∘ B) (c * r)) := by
  obtain ⟨b, hb, hba, hb1, htransfer⟩ :=
    exists_uniform_analytic_chart_transfer (m := m) (n := n) (s := s) ha ha1 hD
  refine ⟨b, hb, hba, hb1, ?_⟩
  intro w A B hA hwA hwB Z Ω hZ F G r κ β c hr hr1 hκ hsmall hβ hβ1 hmargin
    hc hca hF hjac hdet herror hframe hG hmap hAdet hAerror hGjac hinj hcontain
  have hne : (weightedBox (w ∘ A) (β * r)).Nonempty := by
    refine ⟨0, ?_⟩
    intro i
    simp only [Pi.zero_apply, abs_zero]
    positivity
  obtain ⟨Ψ, hΨ, hinverse, _hleft⟩ :=
    exists_continuous_inverse_of_actual_chart_injective (isOpen_weightedBox _ _) hne G hG hGjac hinj
  apply htransfer w A B hA hwA hwB Z Ω hZ F G Ψ r κ β c hr hr1 hκ hsmall
    hβ hβ1 hmargin hc hca hF hjac hdet herror hframe hG hmap hAdet hAerror
    (hΨ.mono hcontain)
  intro u hu
  exact hinverse (F u) (hcontain ⟨u, hu, rfl⟩)

end RothschildStein.G4
