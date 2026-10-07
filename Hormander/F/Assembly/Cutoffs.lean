-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import Hormander.F.Defs
public import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension

/-!
# Nested cutoffs for local regularity

Nested smooth cutoffs inside a ball, built from Mathlib's `ContDiffBump`.
-/

@[expose] public section

noncomputable section

open Filter Set Topology Metric

namespace Hormander.F

/-- Cutoffs `χ`, `ζ'`, `ζ` inside the ball `B(x₀, r)`:
`ζ = 1` on a ball around `x₀`, `ζ' = 1` near `tsupport ζ`, `χ = 1` near `tsupport ζ'`, and
`tsupport χ ⊆ B(x₀, r)`. -/
theorem exists_nested_cutoffs {N : ℕ} (x₀ : E₂ N) {r : ℝ} (hr : 0 < r) :
    ∃ (ζ ζ' χ : E₂ N → ℝ),
      ContDiff ℝ (⊤ : ℕ∞) ζ ∧ ContDiff ℝ (⊤ : ℕ∞) ζ' ∧ ContDiff ℝ (⊤ : ℕ∞) χ ∧
      HasCompactSupport ζ ∧ HasCompactSupport ζ' ∧ HasCompactSupport χ ∧
      (∀ x ∈ ball x₀ (r / 8), ζ x = 1) ∧
      (∀ᶠ x in 𝓝ˢ (tsupport ζ), ζ' x = 1) ∧
      (∀ᶠ x in 𝓝ˢ (tsupport ζ'), χ x = 1) ∧
      tsupport ζ' ⊆ ball x₀ r ∧ tsupport χ ⊆ ball x₀ r := by
  let bζ : ContDiffBump x₀ := ⟨r / 8, r / 4, by positivity, by linarith⟩
  let bζ' : ContDiffBump x₀ := ⟨3 * r / 8, r / 2, by positivity, by linarith⟩
  let bχ : ContDiffBump x₀ := ⟨5 * r / 8, 3 * r / 4, by positivity, by linarith⟩
  have hnhds : ∀ (b : ContDiffBump x₀) (t : Set (E₂ N)) (ρ : ℝ), t ⊆ ball x₀ ρ → ρ ≤ b.rIn →
      ∀ᶠ x in 𝓝ˢ t, (b : E₂ N → ℝ) x = 1 := by
    intro b t ρ ht hρ
    have : ball x₀ ρ ∈ 𝓝ˢ t := isOpen_ball.mem_nhdsSet.2 ht
    filter_upwards [this] with x hx
    exact b.one_of_mem_closedBall (ball_subset_closedBall.trans (closedBall_subset_closedBall hρ) hx)
  refine ⟨bζ, bζ', bχ, bζ.contDiff, bζ'.contDiff, bχ.contDiff, bζ.hasCompactSupport,
    bζ'.hasCompactSupport, bχ.hasCompactSupport, ?_, ?_, ?_, ?_, ?_⟩
  · intro x hx
    exact bζ.one_of_mem_closedBall (ball_subset_closedBall hx)
  · refine hnhds bζ' _ (3 * r / 8) ?_ le_rfl
    rw [bζ.tsupport_eq]
    exact closedBall_subset_ball (by show r / 4 < 3 * r / 8; linarith)
  · refine hnhds bχ _ (5 * r / 8) ?_ le_rfl
    rw [bζ'.tsupport_eq]
    exact closedBall_subset_ball (by show r / 2 < 5 * r / 8; linarith)
  · rw [bζ'.tsupport_eq]
    exact closedBall_subset_ball (by show r / 2 < r; linarith)
  · rw [bχ.tsupport_eq]
    exact closedBall_subset_ball (by show 3 * r / 4 < r; linarith)

end Hormander.F
