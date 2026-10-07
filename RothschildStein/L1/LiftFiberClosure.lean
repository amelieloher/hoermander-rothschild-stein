-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.L1.StarredFiberBounds
public import RothschildStein.L1.StarredComparison
public import RothschildStein.L1.FiberRescalingAssembly

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
namespace RothschildStein.L1

/-- The compact fiber clause of `GaugeFiberData` for every
coordinate data, from compact paired chart buffers (BB pp. 516–522). -/
theorem CoordinateApproximationData.compactFiberBounds_of_chartBuffers {n k s m : ℕ}
    {w : Fin (k+1) → ℕ+} {Ω : Set (Fin n → ℝ)} {X : Fin (k+1) → (Fin n → ℝ) → (Fin n → ℝ)}
    {x₀ : Fin n → ℝ} {L : FixedLiftData w s Ω X x₀ m}
    {M : ModelData (k+1) s (n+m) w} (A : CoordinateApproximationData L M)
    (hn : 0 < n) (hΩ : IsOpen Ω) (hX : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (X i) Ω)
    (hs : 1 ≤ s) (hw : ∀ i, (w i : ℕ) ≤ s) (hbuf : CompactChartBuffers A) :
    CompactFiberBounds A :=
  A.compactFiberBounds_of_starred hΩ hs hw
    (A.starredFiberBounds_of_chartBuffers hn hΩ hX hs hw hbuf)
    (A.compactStarredComparison hn hΩ hX hs hw)

/-- The lifted chart, with the gauge-coordinated data of the
fixed lift; the only remaining input is the compact chart-buffer cover
(BB pp. 483–485, 514–522) (BB pp. 483–485, 514–522). -/
theorem exists_liftedChart_of_chartBuffers {n k : ℕ}
    (w : Fin k → ℕ+) (s : ℕ) (hn : 0 < n) (hk : 0 < k) (hw : ∀ i, (w i : ℕ) ≤ s)
    (Ω : Set (Fin n → ℝ)) (hΩ : IsOpen Ω)
    (X : Fin k → (Fin n → ℝ) → (Fin n → ℝ))
    (hX : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (X i) Ω)
    (x₀ : Fin n → ℝ) (hx₀ : x₀ ∈ Ω) (hspan : StepSpansAt w s X x₀)
    (hbuf : ∀ (m : ℕ) (L : FixedLiftData w s Ω X x₀ m)
      (M : ModelData k s (n+m) w) (A : CoordinateApproximationData L M), CompactChartBuffers A) :
    ∃ m : ℕ, n+m = freeDimension k s w ∧ Nonempty (P1.LiftedChart w s Ω hΩ X x₀ m) := by
  refine exists_liftedChart_of_fiberBounds w s hk hw Ω hΩ X hX x₀ hx₀ hspan ?_
  intro m L M A
  obtain ⟨k, rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
  exact A.compactFiberBounds_of_chartBuffers hn hΩ hX (le_trans (w 0).pos (hw 0)) hw
    (hbuf m L M A)

end RothschildStein.L1
