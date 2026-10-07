-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import Hormander.Defs.LieWordEval
public import Hormander.Defs.LieWordLength
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.Calculus.ContDiff.Basic
public import Mathlib.Topology.Algebra.Support

@[expose] public section

noncomputable section

namespace Hormander.F

open Hormander.Interface
open Filter Set Topology

abbrev E₂ (N : ℕ) := EuclideanSpace ℝ (Fin N)

/-- The single local frame patch and coefficient extension used by the
local regularity argument. The fields record an actual ball, one cutoff equal to one near its
closure, compactly supported smooth coefficient extensions agreeing with the original fields near
that closure, and one finite Lie-word frame with its fixed step and gain. -/
structure LocalPatch {k N : ℕ} (hN : 0 < N) (Ω : Set (E₂ N))
    (X : Fin (k + 1) → E₂ N → E₂ N) (c : E₂ N → ℝ) (x₀ : E₂ N) where
  radius : ℝ
  radius_pos : 0 < radius
  ball_closure_subset : closure (Metric.ball x₀ radius) ⊆ Ω
  cutoff : E₂ N → ℝ
  cutoff_smooth : ContDiff ℝ (⊤ : ℕ∞) cutoff
  cutoff_compact : HasCompactSupport cutoff
  cutoff_tsupport : tsupport cutoff ⊆ Ω
  cutoff_one_near_ball : ∀ᶠ x in 𝓝ˢ (closure (Metric.ball x₀ radius)), cutoff x = 1
  extendedX : Fin (k + 1) → E₂ N → E₂ N
  extendedX_smooth : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (extendedX i)
  extendedX_compact : ∀ i, HasCompactSupport (extendedX i)
  extendedX_eq_near_ball : ∀ i,
    ∀ᶠ x in 𝓝ˢ (closure (Metric.ball x₀ radius)), extendedX i x = X i x
  extendedC : E₂ N → ℝ
  extendedC_smooth : ContDiff ℝ (⊤ : ℕ∞) extendedC
  extendedC_compact : HasCompactSupport extendedC
  extendedC_eq_near_ball : ∀ᶠ x in 𝓝ˢ (closure (Metric.ball x₀ radius)),
    extendedC x = c x
  words : Fin N → LieWord k
  frame_on_ball : ∀ x ∈ Metric.ball x₀ radius,
    LinearIndependent ℝ (fun a => lieWordEval extendedX (words a) x)
  step : ℕ
  step_eq : step = Finset.univ.sup (fun a : Fin N => lieWordLength (words a))
  word_length_le_step : ∀ a, lieWordLength (words a) ≤ step
  gain : ℝ
  gain_eq : gain = 2 / (4 : ℝ) ^ step

end Hormander.F
