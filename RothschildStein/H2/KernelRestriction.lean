-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H2.LocalKernelData

set_option autoImplicit false
set_option relaxedAutoImplicit false

@[expose] public section
noncomputable section
open Set MeasureTheory Metric

namespace RothschildStein.H2
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]

omit [BorelSpace X] in
/-- Restricting a kernel class to a measurable subset retains its constants. -/
theorem KernelClass.restrict {μ : Measure X} {E G : Set X} {β ν A S : ℝ} {K : X → X → ℝ}
    (hK : KernelClass μ G β ν A S K) (hE : MeasurableSet E) (hEG : E ⊆ G) :
    KernelClass μ E β ν A S K := by
  let j : E → G := fun x => ⟨x, hEG x.property⟩
  have hj : Measurable j := measurable_subtype_coe.subtype_mk
  refine ⟨hE, hK.measurable.comp ((hj.comp measurable_fst).prodMk (hj.comp measurable_snd)),
    hK.β_pos, hK.β_le_one, hK.ν_nonneg, hK.A_nonneg, hK.S_nonneg, ?_, ?_⟩
  · intro x hx y hy hxy
    exact hK.size x (hEG hx) y (hEG hy) hxy
  · intro x₀ hx₀ x hx y hy hs
    exact hK.smooth x₀ (hEG hx₀) x (hEG hx) y (hEG hy) hs

omit [MetricSpace X] [MeasurableSpace X] [BorelSpace X] in
/-- Localization distributes over the sum of kernel pieces. -/
theorem localizedKernel_add (U : Set X) (a b : X → ℝ) (K₀ K₁ : X → X → ℝ) :
    localizedKernel U a b (fun x y => K₀ x y + K₁ x y) =
      fun x y => localizedKernel U a b K₀ x y + localizedKernel U a b K₁ x y := by
  classical
  funext x y
  unfold localizedKernel
  split_ifs <;> ring

omit [MeasurableSpace X] [BorelSpace X] in
/-- A localized kernel vanishes at distances at least the ball diameter. -/
theorem localizedKernel_support {z : X} {R : ℝ} (a b : X → ℝ) (K : X → X → ℝ)
    {x y : X} (hr : 2 * R ≤ dist x y) : localizedKernel (ball z R) a b K x y = 0 := by
  classical
  unfold localizedKernel
  split_ifs with h
  · exact False.elim (not_lt_of_ge hr (dist_lt_two_radius h.1 h.2))
  · rfl

end RothschildStein.H2
