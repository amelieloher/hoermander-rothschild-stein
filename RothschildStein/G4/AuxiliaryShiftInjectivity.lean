-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.G4.UniformChartTransferShrinkage

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set Function

namespace RothschildStein.G4

/-- After the zero-shift frame chain, one proved same-frame
transfer gives injectivity of the requested small auxiliary shift.
All analytic and trajectory estimates stay at the requested original
radius (BB Prop 9.55, pp. 456–458). -/
theorem auxiliary_shift_chart_injective_of_zero_shift {m n s : ℕ}
    {α a c D : ℝ} (ha : 0 < a) (htransfer : ChartTransferRule m n s α a c D)
    (w : Fin m → ℕ+) (B : Fin n → Fin m) (hwB : ∀ i, (w (B i) : ℕ) ≤ s)
    (Z : Fin m → (Fin n → ℝ) → (Fin n → ℝ)) (Ω : Set (Fin n → ℝ))
    (hZ : ∀ J, ContinuousOn (Z J) Ω)
    (F G : (Fin n → ℝ) → (Fin n → ℝ)) {r κ : ℝ}
    (hr : 0 < r) (hr1 : r ≤ 1) (hκ : 0 ≤ κ) (hsmall : (n : ℝ) * κ ≤ 1 / 4)
    (hF : ChartAnalyticBounds Ω w Z B F (weightedBox (w ∘ B) (a * r)) r κ D)
    (hG : ChartAnalyticBounds Ω w Z B G (weightedBox (w ∘ B) (a * r)) r κ D)
    (hinj : InjOn G (weightedBox (w ∘ B) (α * r)))
    (x : Fin n → ℝ) (hGzero : G 0 = x) (v : Fin m → ℝ)
    (hv : v ∈ weightedBox w (c * r))
    (ΓF ΓG : (Fin n → ℝ) → ℝ → (Fin n → ℝ))
    (hΓF : ChartTrajectories Ω Z B F (weightedBox (w ∘ B) (a * r)) x v ΓF)
    (hΓG : ChartTrajectories Ω Z B G (weightedBox (w ∘ B) (a * r)) x 0 ΓG) :
    InjOn F (weightedBox (w ∘ B) (c * r)) := by
  have hz : (0 : Fin n → ℝ) ∈ weightedBox (w ∘ B) (a * r) := by
    intro i
    simp only [Pi.zero_apply, abs_zero]
    exact pow_pos (mul_pos ha hr) _
  have hdet : frameDet Z B x ≠ 0 := by
    simpa only [hGzero] using hG.2.2.2.1 0 hz
  exact htransfer w B B (frame_index_injective_of_frameDet_ne_zero Z B hdet)
    hwB hwB Z Ω hZ F G r κ hr hr1 hκ hsmall hF hG hinj x hGzero hdet
    v hv ΓF ΓG hΓF hΓG

end RothschildStein.G4
