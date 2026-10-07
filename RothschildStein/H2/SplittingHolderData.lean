-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H2.SplittingCancellation
public import RothschildStein.H2.CutoffHolderBounds
public import RothschildStein.H2.PrincipalValueHolder

set_option autoImplicit false
set_option relaxedAutoImplicit false

@[expose] public section
noncomputable section
open Set MeasureTheory Metric
open scoped NNReal ENNReal

namespace RothschildStein.H2
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
variable {D : LocDoubling X} {d : TruncDist D}

/-- The localized fractional smoothness constant. -/
def LocalKernelData.fractionalS (Q : LocalKernelData D d) : ℝ :=
  Q.S₁ + 4 * Q.R * (Q.Lₐ : ℝ) * D.C_D ^ 2 * (3 / 2 : ℝ) ^ Q.ν * Q.A₁

/-- The localized fractional piece satisfies the supported-kernel hypotheses on the cutoff ball. -/
theorem LocalKernelData.supported_localized_fractional (Q : LocalKernelData D d) :
    SupportedKernel D (ball Q.z Q.R) (ball Q.z Q.R) Q.β Q.ν Q.A₁ Q.fractionalS (2 * Q.R)
      (localizedKernel (ball Q.z Q.R) Q.a Q.b Q.K₁) := by
  have hsub : ball Q.z Q.R ⊆ ball Q.z (2 * Q.R) := ball_subset_ball (by linarith [Q.radius_pos])
  have hk := localized_kernelClass D Q.center Q.radius_pos Q.radius_lt Q.cutoff_a Q.cutoff_b
    (Q.fractional.restrict isOpen_ball.measurableSet hsub)
  refine ⟨isOpen_ball.measurableSet, subset_rfl, hsub.trans Q.doubledBall_subset,
    by linarith [Q.radius_pos], by linarith [Q.radius_lt, D.κ_pos],
    hk.restrict isOpen_ball.measurableSet (hsub.trans Q.doubledBall_subset), ?_⟩
  intro x _ y _ hr
  exact localizedKernel_support _ _ _ hr

/-- The regularized singular piece has cancellation constant zero
on the doubled input ball. -/
theorem LocalKernelData.singular_shellCancellation (Q : LocalKernelData D d) :
    ShellCancellation D.μ (ball Q.z Q.R) (ball Q.z (2 * Q.R)) d.d' Q.K₀ 0 := by
  refine ⟨le_rfl, ?_⟩
  intro x hx r₁ r₂ h₁ h₁₂
  rw [Q.vanishing_all hx h₁ h₁₂, abs_zero]

/-- Explicit universal Hölder bound for T(1), written with
L_a=Λ_a/R and L_b=Λ_b/R. BB Proposition 7.17, p. 308. -/
def LocalKernelData.oneHolderConstant (Q : LocalKernelData D d) (γ : ℝ) : ℝ :=
  (1 + (Q.Lₐ : ℝ) * (2 * Q.R) ^ (1 - γ)) *
    ((Q.Lᵦ : ℝ) * (4 * Q.R) ^ (1 - γ)) *
    (regularizedHolderConstant Q.β₀ γ D.C_D d.θ₁ d.θ₂ * (Q.A₀ + Q.S₀) +
      volumeIntegralConstant D.C_D γ * Q.A₀ * Q.R ^ γ) +
    fractionalHolderConstant D.C_D D.κ (2 * Q.R) γ Q.ν * (Q.A₁ + Q.fractionalS)

end RothschildStein.H2
