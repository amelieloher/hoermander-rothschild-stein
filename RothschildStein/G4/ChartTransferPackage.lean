-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.G4.ChartAnalyticData
public import RothschildStein.G4.UniformInjectivityTransfer
public import RothschildStein.G4.ChartImageContainment
public import RothschildStein.G4.TransferRadiusChoices

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set Function
open scoped ENNReal

namespace RothschildStein.G4

/-- Uniform pointwise transfer from actual analytic and trajectory
packages. All shrinkages precede the fields and charts, and both image
inclusions and the inverse are constructed (BB pp. 456–458). -/
theorem exists_uniform_chart_transfer_with_trajectories {m n s : ℕ}
    {α a D : ℝ} (hα : 0 < α) (hα1 : α ≤ 1)
    (ha : 0 < a) (ha1 : a ≤ 1) (hD : 0 ≤ D) :
    ∃ β c : ℝ, 0 < β ∧ β ≤ α ∧ 0 < c ∧ c < a / 4 ∧
      ∀ (w : Fin m → ℕ+) (A B : Fin n → Fin m), Injective A →
        (∀ i, (w (A i) : ℕ) ≤ s) → (∀ i, (w (B i) : ℕ) ≤ s) →
      ∀ (Z : Fin m → (Fin n → ℝ) → (Fin n → ℝ)) (Ω : Set (Fin n → ℝ)),
        (∀ J, ContinuousOn (Z J) Ω) →
      ∀ (F G : (Fin n → ℝ) → (Fin n → ℝ)) (r κ : ℝ),
        0 < r → r ≤ 1 → 0 ≤ κ → (n : ℝ) * κ ≤ 1 / 4 →
        ChartAnalyticBounds Ω w Z B F (weightedBox (w ∘ B) (a * r)) r κ D →
        ChartAnalyticBounds Ω w Z A G (weightedBox (w ∘ A) (β * r)) r κ D →
        InjOn G (weightedBox (w ∘ A) (α * r)) →
      ∀ (x : Fin n → ℝ), G 0 = x → frameDet Z B x ≠ 0 →
      ∀ v : Fin m → ℝ, v ∈ weightedBox w (c * r) →
      ∀ (ΓF ΓG : (Fin n → ℝ) → ℝ → (Fin n → ℝ)),
        ChartTrajectories Ω Z B F (weightedBox (w ∘ B) (c * r)) x v ΓF →
        ChartTrajectories Ω Z A G (weightedBox (w ∘ A) (β * r)) x 0 ΓG →
        InjOn F (weightedBox (w ∘ B) (c * r)) := by
  obtain ⟨b, hb, _hba, hb1, htransfer⟩ :=
    exists_uniform_actual_chart_injectivity_transfer (m := m) (n := n) (s := s) ha ha1 hD
  obtain ⟨β, hβ, hβα, hβ1, hmargin⟩ :=
    exists_small_contraction_radius s (d := 2 * b) hα hα1 (mul_pos (by norm_num) hb)
  obtain ⟨bOld, hbOld, hbOldβ, _hbOld1, hlift⟩ :=
    exists_uniform_controlled_chart_lift_radius (m := m) (n := n) (s := s) hβ hβ1 hD
  obtain ⟨c, hc, hca, hcb⟩ := exists_small_transfer_image_radius ha hbOld
  refine ⟨β, c, hβ, hβα, hc, hca, ?_⟩
  intro w A B hA hwA hwB Z Ω hZ F G r κ hr hr1 hκ hsmall hFB hGA hinj x hGzero hBx
    v hv ΓF ΓG hΓF hΓG
  obtain ⟨hF, _hFmap, hFjac, hFdet, hFerror, hFframe⟩ := hFB
  obtain ⟨hG, hGmap, hGjac, hGdet, hGerror, hGframe⟩ := hGA
  have hzero : (0 : Fin n → ℝ) ∈ weightedBox (w ∘ A) (β * r) := by
    intro i
    simp only [Pi.zero_apply, abs_zero]
    positivity
  have hAx : frameDet Z A x ≠ 0 := by simpa only [hGzero] using hGdet 0 hzero
  have hvzero : (0 : Fin m → ℝ) ∈ weightedBox w (bOld * r) := by
    intro i
    simp only [Pi.zero_apply, abs_zero]
    positivity
  have hinner := (shifted_chart_ball_inclusions Ω w Z A G hAx hβ hbOld
    (by linarith) hr 0 hvzero ΓG hΓG (fun γ hγ hstart => by
      obtain ⟨θ, hθ, _, _⟩ := hlift w A hwA Z G r κ hr hr1 hκ hsmall hG hGjac
        hGdet hGerror hGframe Ω γ hγ hstart
      exact ⟨θ, hθ⟩)).1
  have hupper := chart_image_control_ball_subset_of_trajectories Ω w Z B F hBx hc hr
    v hv ΓF hΓF
  have hcontain := chart_image_subset_of_control_ball_inclusions Ω w Z F G hr.le hcb.le
    hupper hinner
  have hGinj : InjOn G (weightedBox (w ∘ A) (β * r)) := hinj.mono (by
    intro u hu i
    exact (hu i).trans_le (pow_le_pow_left₀ (mul_nonneg hβ.le hr.le)
      (mul_le_mul_of_nonneg_right hβα hr.le) _))
  exact htransfer w A B hA hwA hwB Z Ω hZ F G r κ β c hr hr1 hκ hsmall hβ hβ1
    hmargin hc.le hca.le hF hFjac hFdet hFerror hFframe hG hGmap hGdet hGerror
    hGjac hGinj hcontain

end RothschildStein.G4
