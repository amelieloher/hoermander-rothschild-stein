-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Moser.HolderParabolicPairComparison
public import HeatKernel.Moser.HolderCommonFullMeasureSet
import Mathlib.Tactic

/-! # A common full-measure parabolic Hölder set from rational-cylinder decay -/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open MeasureTheory Set Metric Filter
namespace HeatKernel

/-- Countably many rational-cylinder oscillations and geometric decay give one
full-measure dense set with a normalized parabolic Hölder modulus. The decay and
its comparison with essential oscillations are explicit analytic hypotheses. -/
theorem exists_dense_full_measure_parabolic_holder_set
    {X : Type*} [MetricSpace X] (c : ℕ → X) (hc : DenseRange c)
    {Ω : Set (ParabolicSpaceTime X)} [MeasurableSpace Ω]
    (μ : Measure Ω) [μ.IsOpenPosMeasure]
    (u : ℝ × X → ℝ) (ω : ℝ → X → ℝ → ℝ)
    {x₀ : X} {top r a θ W : ℝ}
    (hr : 0 < r) (ha : 0 ≤ a) (hθ : 0 ≤ θ)
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
    ∃ s : Set Ω, (∀ᵐ z ∂μ, z ∈ s) ∧ Dense s ∧
      ∀ z ∈ s, ∀ w ∈ s,
        |u (z.val.1.val, z.val.2) - u (w.val.1.val, w.val.2)| ≤
          (1024 / 15 : ℝ) ^ a * (dist z w / r) ^ a * W := by
  let Q : Option (ℚ × ℚ × ℕ) → Set Ω := fun j => match j with
    | none => univ
    | some (τ, ρ, i) => {z | (z.val.1.val, z.val.2) ∈
        Ioo ((τ : ℝ) - (ρ : ℝ) ^ 2) τ ×ˢ ball (c i) ρ}
  let f : Ω → ℝ := fun z => u (z.val.1.val, z.val.2)
  obtain ⟨s, hs, hdense, hpairs⟩ :=
    exists_dense_full_measure_set_pair_oscillation μ Q f
      (fun _ => hupper.mono (ae_mono Measure.restrict_le_self))
      (fun _ => hlower.mono (ae_mono Measure.restrict_le_self))
  refine ⟨s, hs, hdense, ?_⟩
  intro z hz w hw
  have hwhole := hpairs none z w hz hw (mem_univ _) (mem_univ _)
  have hbound : |f z - f w| ≤ W := by
    have hwhole' : |f z - f w| ≤ essSup f μ - essInf f μ := by
      simpa only [Q, Measure.restrict_univ] using hwhole
    exact hwhole'.trans hglobal
  have hzt := hΩ z.val z.property
  have hwt := hΩ w.val w.property
  exact abs_sub_le_of_parabolic_rational_cylinder_oscillation c hc u ω z.val w.val
    hr hzt.1 hzt.2.1 (max_lt hzt.2.2 hwt.2.2) ha hθ hθa hW hbound
    (fun τ ρ i hzi hwi =>
      (hpairs (some (τ, ρ, i)) z w hz hw hzi hwi).trans (hosc τ ρ i)) hmono hdecay

end HeatKernel
