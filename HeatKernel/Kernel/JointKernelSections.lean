-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Analysis.Calculus.ContDiff.Comp

/-! # Fixed-endpoint sections of jointly smooth kernels -/

@[expose] public section

namespace HeatKernel

variable {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y]

/-- Fixing the first spatial endpoint preserves positive-time joint kernel smoothness. -/
theorem contDiffOn_joint_kernel_row
    (p : ℝ → X → Y → ℝ)
    (hp : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : ℝ × (X × Y) => p z.1 z.2.1 z.2.2)
      (Set.Ioi 0 ×ˢ Set.univ)) (x : X) :
    ContDiffOn ℝ (⊤ : ℕ∞) (fun z : ℝ × Y => p z.1 x z.2) {z | 0 < z.1} := by
  exact hp.comp (contDiff_fst.prodMk (contDiff_const.prodMk contDiff_snd)).contDiffOn
    (fun z hz => ⟨hz, Set.mem_univ (x, z.2)⟩)

/-- Fixing the second spatial endpoint preserves positive-time joint kernel smoothness. -/
theorem contDiffOn_joint_kernel_column
    (p : ℝ → X → Y → ℝ)
    (hp : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : ℝ × (X × Y) => p z.1 z.2.1 z.2.2)
      (Set.Ioi 0 ×ˢ Set.univ)) (y : Y) :
    ContDiffOn ℝ (⊤ : ℕ∞) (fun z : ℝ × X => p z.1 z.2 y) {z | 0 < z.1} := by
  exact hp.comp (contDiff_fst.prodMk (contDiff_snd.prodMk contDiff_const)).contDiffOn
    (fun z hz => ⟨hz, Set.mem_univ (z.2, y)⟩)

end HeatKernel
