-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H2.KernelRestriction
public import RothschildStein.H2.KernelSupport

set_option autoImplicit false
set_option relaxedAutoImplicit false

@[expose] public section
noncomputable section
open Set MeasureTheory Metric
open scoped NNReal

namespace RothschildStein.H2
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
variable {D : LocDoubling X} {d : TruncDist D}

/-- The singular size constant after the fractional piece is localized. -/
def LocalKernelData.singularA (Q : LocalKernelData D d) : ℝ := Q.A₀ + Q.A₁ * (2 * Q.R) ^ Q.ν

/-- The singular smoothness constant after localization and summation. -/
def LocalKernelData.singularS (Q : LocalKernelData D d) : ℝ :=
  (Q.S₀ + 4 * Q.R * (Q.Lₐ : ℝ) * D.C_D ^ 2 * Q.A₀) +
  (Q.S₁ + 4 * Q.R * (Q.Lₐ : ℝ) * D.C_D ^ 2 * (3 / 2 : ℝ) ^ Q.ν * Q.A₁) * (4 * Q.R) ^ Q.ν

/-- The localized sum is a singular kernel with explicit constants (BB Proposition 7.17, pp. 306–308), using the radial weight estimates. -/
theorem LocalKernelData.localized_singular (Q : LocalKernelData D d) :
    KernelClass D.μ D.Ω₁ (min Q.β₀ Q.β) 0 Q.singularA Q.singularS Q.cutoffKernel := by
  have hsub : ball Q.z Q.R ⊆ ball Q.z (2 * Q.R) :=
    ball_subset_ball (by linarith [Q.radius_pos])
  have h₀ := localized_singular_kernelClass D Q.center Q.radius_pos Q.radius_lt Q.cutoff_a Q.cutoff_b
    (Q.singular.restrict isOpen_ball.measurableSet hsub)
  have h₁ := localized_kernelClass D Q.center Q.radius_pos Q.radius_lt Q.cutoff_a Q.cutoff_b
    (Q.fractional.restrict isOpen_ball.measurableSet hsub)
  have hs := h₁.singular_of_support (R := 2 * Q.R) (by linarith [Q.radius_pos])
    (fun x _ y _ hr => localizedKernel_support _ _ _ hr)
  have he := h₀.add hs
  change KernelClass _ _ _ _ _ _ (localizedKernel _ _ _ (fun x y => Q.K₀ x y + Q.K₁ x y))
  rw [localizedKernel_add]
  simpa only [LocalKernelData.singularA, LocalKernelData.singularS,
    show 2 * (2 * Q.R) = 4 * Q.R by ring] using he

end RothschildStein.H2
