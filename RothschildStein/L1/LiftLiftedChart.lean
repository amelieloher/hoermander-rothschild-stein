-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.L1.LiftFiberClosure
public import RothschildStein.L1.LiftChartBufferCover

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
namespace RothschildStein.L1

/-- The fixed lift, its matching free model and coordinate data
carrying the ambient gauge comparison and the compact ball/fiber bounds assemble to
the lifted chart (BB pp. 483–485, 506–522). -/
theorem exists_liftedChart {n k : ℕ}
    (w : Fin k → ℕ+) (s : ℕ) (hn : 0 < n) (hk : 0 < k) (hw : ∀ i, (w i : ℕ) ≤ s)
    (Ω : Set (Fin n → ℝ)) (hΩ : IsOpen Ω)
    (X : Fin k → (Fin n → ℝ) → (Fin n → ℝ))
    (hX : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (X i) Ω)
    (x₀ : Fin n → ℝ) (hx₀ : x₀ ∈ Ω) (hspan : StepSpansAt w s X x₀) :
    ∃ m : ℕ, n+m = freeDimension k s w ∧ Nonempty (P1.LiftedChart w s Ω hΩ X x₀ m) := by
  have hs : 1 ≤ s := le_trans (w ⟨0, hk⟩).pos (hw ⟨0, hk⟩)
  refine exists_liftedChart_of_chartBuffers w s hn hk hw Ω hΩ X hX x₀ hx₀ hspan ?_
  intro m L M A
  obtain ⟨k, rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
  exact A.compactChartBuffers_of_cover hn hΩ hX hs

end RothschildStein.L1
