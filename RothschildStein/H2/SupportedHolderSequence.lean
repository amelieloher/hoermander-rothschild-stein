-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H2.SupportedHolderDensity

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set MeasureTheory Metric Filter
open scoped ENNReal NNReal Topology

namespace RothschildStein.H2
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
variable {D : LocDoubling X} {d : TruncDist D}

/-- A supported L² input has a sequence of bounded Hölder
approximations supported in the doubled ball, converging in L². -/
theorem LocalKernelData.exists_supported_holder_sequence (Q : LocalKernelData D d)
    {δ : ℝ≥0} (hδ : 0 < δ) (hδ₁ : δ ≤ 1) (z : X) {r : ℝ} (hr : 0 < r)
    (v : Lp ℝ 2 (D.μ.restrict (ball Q.z Q.R)))
    (hv : ∀ᵐ x ∂D.μ.restrict (ball Q.z Q.R), x ∉ ball z r → v x = 0) :
    ∃ f : ℕ → holderFunctions δ (ball Q.z Q.R),
      (∀ n x, x ∉ ball z (2 * r) → (f n : X → ℝ) x = 0) ∧
      Tendsto (fun n => holderL2 δ (ball Q.z Q.R) D.μ hδ isOpen_ball.measurableSet
        Q.measure_ball_lt_top (f n)) atTop (𝓝 v) := by
  have he : ∀ n : ℕ, 0 < 1 / ((n : ℝ) + 1) := fun n => by positivity
  choose f hs hn using fun n => Q.exists_supported_holder_approx hδ hδ₁ z hr v hv (he n)
  refine ⟨f, hs, ?_⟩
  apply tendsto_iff_dist_tendsto_zero.mpr
  simp only [dist_eq_norm]
  exact squeeze_zero (fun _ => norm_nonneg _) (fun n => (hn n).le)
    tendsto_one_div_add_atTop_nhds_zero_nat

end RothschildStein.H2
