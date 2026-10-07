-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.G4.TranslatedChartAnalyticBounds

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set

namespace RothschildStein.G4

/-- The numerical lifting radius also works from every initial
coordinate in the quarter-size box. Translate the chart, apply the
proved zero-start lift, and translate back (BB Prop 9.55, pp. 457–458). -/
theorem exists_uniform_controlled_lift_from_small_start {m n s : ℕ}
    {a D : ℝ} (ha : 0 < a) (ha1 : a ≤ 1) (hD : 0 ≤ D) :
    ∃ b : ℝ, 0 < b ∧ b < a / 8 ∧ 2 * b ≤ 1 ∧
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
        ∀ (u₀ : Fin n → ℝ), u₀ ∈ weightedBox (w ∘ B) (a / 4 * r) →
        ∀ (Ω : Set (Fin n → ℝ)) (γ : ℝ → (Fin n → ℝ)),
          isControlledCurve Ω w Z (2 * b * r) γ → F u₀ = γ 0 →
          ∃ θ : ℝ → (Fin n → ℝ),
            ContinuousOn θ (Icc (0 : ℝ) 1) ∧ θ 0 = u₀ ∧
            MapsTo θ (Icc (0 : ℝ) 1) (weightedBox (w ∘ B) (a * r)) ∧
            EqOn (F ∘ θ) γ (Icc (0 : ℝ) 1) ∧
            AbsolutelyContinuousOnInterval θ 0 1 := by
  obtain ⟨b, hb, hba, hb1, hlift⟩ :=
    exists_uniform_controlled_chart_lift_radius (m := m) (n := n) (s := s)
      (a := a / 2) (half_pos ha) (by linarith) hD
  refine ⟨b, hb, by linarith, hb1, ?_⟩
  intro w B hw Z F r κ hr hr1 hκ hsmall hF hjac hdet herror hframe u₀ hu₀ Ω γ hγ hstart
  let G : (Fin n → ℝ) → (Fin n → ℝ) := fun u => F (u + u₀)
  have hmap : ∀ u ∈ weightedBox (w ∘ B) (a / 2 * r),
      u + u₀ ∈ weightedBox (w ∘ B) (a * r) :=
    fun u hu => weightedBox_half_add_quarter_mem (w ∘ B) ha.le hr.le hu hu₀
  obtain ⟨hG, hder⟩ := translated_chart_smooth_derivative (w ∘ B) ha.le hr.le F hF hu₀
  have hGjac : ∀ u ∈ weightedBox (w ∘ B) (a / 2 * r),
      Matrix.det (coordinateDerivativeMatrix (fderiv ℝ G u)) ≠ 0 := by
    intro u hu
    rw [hder]
    exact hjac _ (hmap u hu)
  have hGerror : ∀ u ∈ weightedBox (w ∘ B) (a / 2 * r), ∀ i j,
      |frameCoefficient Z B
        (fun z => fderiv ℝ G u (Pi.single j 1) - Z (B j) z) i (G u)| ≤
          κ * r ^ (((w (B i) : ℕ) : ℤ) - ((w (B j) : ℕ) : ℤ)) := by
    intro u hu i j
    rw [hder]
    exact herror _ (hmap u hu) i j
  obtain ⟨θ, hθ, hAC, _hhalf⟩ := hlift w B hw Z G r κ hr hr1 hκ hsmall hG hGjac
    (fun u hu => hdet _ (hmap u hu)) hGerror
    (fun u hu => hframe _ (hmap u hu)) Ω γ hγ (by simpa [G] using hstart)
  refine ⟨fun t => θ t + u₀, hθ.1.add continuousOn_const,
    by change θ 0 + u₀ = u₀; rw [hθ.2.1, zero_add], ?_, ?_, ?_⟩
  · intro t ht
    exact hmap _ (hθ.2.2.1 ht)
  · intro t ht
    exact hθ.2.2.2 ht
  · exact hAC.add (LipschitzWith.const u₀).lipschitzOnWith.absolutelyContinuousOnInterval

end RothschildStein.G4
