-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module
public import RothschildStein.G3.ZeroCoefficientFlow

@[expose] public section
noncomputable section
open Set Metric Filter
open scoped Topology
namespace RothschildStein.G3

theorem exponential_map_contDiffAt_of_input
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {m N : ℕ} {ε : ℝ} {x₀ : Fin N → ℝ} {z₀ : E}
    {Φ : (((Fin m → ℝ) × (Fin N → ℝ)) × ℝ) → (Fin N → ℝ)}
    {H : E → ((Fin m → ℝ) × (Fin N → ℝ))}
    (hε : 0 < ε) (hH : ContDiffAt ℝ (⊤ : ℕ∞) H z₀) (hbase : H z₀ = (0, x₀))
    (hΦ : ContDiffOn ℝ (⊤ : ℕ∞) Φ ((ball 0 ε ×ˢ ball x₀ ε) ×ˢ Ioo (-2) 2)) :
    ContDiffAt ℝ (⊤ : ℕ∞) (finiteLieTimeOneMap Φ ∘ H) z₀ := by
  have hz : H z₀ ∈ ball 0 ε ×ˢ ball x₀ ε := by rw [hbase]; simp [hε]
  have hU : ball (0 : Fin m → ℝ) ε ×ˢ ball x₀ ε ∈ 𝓝 (H z₀) :=
    (Metric.isOpen_ball.prod Metric.isOpen_ball).mem_nhds hz
  exact ((finiteLieTimeOneMap_contDiffOn hΦ).contDiffAt hU).comp z₀ hH

end RothschildStein.G3
