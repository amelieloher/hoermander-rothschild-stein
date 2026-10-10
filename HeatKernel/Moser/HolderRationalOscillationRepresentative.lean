-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Moser.HolderDenseParabolicModulus
public import HeatKernel.Moser.HolderNormalizedRepresentative
import Mathlib.Tactic

/-! # Continuous parabolic representatives from rational-cylinder decay -/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open MeasureTheory Set Metric Filter
namespace HeatKernel

/-- Rational-cylinder oscillation decay gives a continuous representative on the
interior parabolic domain. All geometric decay inputs remain explicit, and the
radius-normalized modulus retains the original oscillation scale. -/
theorem exists_continuous_parabolic_representative_of_rational_oscillation_decay
    {X : Type*} [MetricSpace X] (c : ℕ → X) (hc : DenseRange c)
    {Ω : Set (ParabolicSpaceTime X)} [MeasurableSpace Ω]
    (μ : Measure Ω) [μ.IsOpenPosMeasure]
    (u : ℝ × X → ℝ) (ω : ℝ → X → ℝ → ℝ)
    {x₀ : X} {top r a θ W : ℝ}
    (hr : 0 < r) (ha : 0 < a) (hθ : 0 ≤ θ)
    (hθa : θ ≤ (1 / 2 : ℝ) ^ a) (hW : 0 ≤ W)
    (hΩ : ∀ z ∈ Ω, dist z.2 x₀ < r ∧ top - r ^ 2 < z.1.val ∧ z.1.val < top)
    (hupper : IsBoundedUnder (· ≤ ·) (ae μ) (fun z => u (z.val.1.val, z.val.2)))
    (hlower : IsBoundedUnder (· ≥ ·) (ae μ) (fun z => u (z.val.1.val, z.val.2)))
    (hglobal : essSup (fun z : Ω => u (z.val.1.val, z.val.2)) μ -
      essInf (fun z : Ω => u (z.val.1.val, z.val.2)) μ ≤ W)
    (hosc : ∀ (τ ρ : ℚ) (i : ℕ),
      let Q : Set Ω := {z | (z.val.1.val, z.val.2) ∈
        Ioo ((τ : ℝ) - (ρ : ℝ) ^ 2) τ ×ˢ ball (c i) ρ}
      essSup (fun z : Ω => u (z.val.1.val, z.val.2)) (μ.restrict Q) -
        essInf (fun z : Ω => u (z.val.1.val, z.val.2)) (μ.restrict Q) ≤ ω τ (c i) ρ)
    (hmono : ∀ τ i, MonotoneOn (ω τ (c i)) (Icc 0 (15 * r / 32)))
    (hdecay : ∀ τ i,
      Ioo (τ - 4 * (15 * r / 32) ^ 2) τ ×ˢ ball (c i) (2 * (15 * r / 32)) ⊆
        Ioo (top - 4 * r ^ 2) top ×ˢ ball x₀ (2 * r) →
      ∀ n : ℕ, ω τ (c i) ((15 * r / 32) * (1 / 2 : ℝ) ^ n) ≤ θ ^ n * W) :
    ∃ v : Ω → ℝ, Continuous v ∧
      v =ᵐ[μ] (fun z => u (z.val.1.val, z.val.2)) ∧
      ∀ z w, |v z - v w| ≤
        (1024 / 15 : ℝ) ^ a * (dist z w / r) ^ a * W := by
  obtain ⟨s, hs, _hdense, hbound⟩ :=
    exists_dense_full_measure_parabolic_holder_set c hc μ u ω
      hr ha.le hθ hθa hW hΩ hupper hlower hglobal hosc hmono hdecay
  exact exists_continuous_representative_of_normalized_holder_bound
    μ (fun z => u (z.val.1.val, z.val.2))
    (Real.rpow_nonneg (by norm_num) _) ha hr hW hs hbound

end HeatKernel
