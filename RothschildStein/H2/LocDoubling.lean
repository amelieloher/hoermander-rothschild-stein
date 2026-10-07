-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import Mathlib.MeasureTheory.Measure.Regular
public import Mathlib.MeasureTheory.Measure.Typeclasses.NullSingletonClass
public import Mathlib.Topology.MetricSpace.ProperSpace

set_option autoImplicit false
set_option relaxedAutoImplicit false

@[expose] public section

open Set MeasureTheory Metric
open scoped ENNReal

namespace RothschildStein.H2

/-- The fixed locally doubling data, with finite outer measure recorded explicitly (BB Definition 7.1, p. 295). -/
structure LocDoubling (X : Type*) [MetricSpace X] [MeasurableSpace X] [BorelSpace X] where
  μ : Measure X
  Ω₀ : Set X
  Ω₁ : Set X
  Ω₂ : Set X
  open₀ : IsOpen Ω₀
  open₁ : IsOpen Ω₁
  open₂ : IsOpen Ω₂
  sub₀₁ : Ω₀ ⊆ Ω₁
  sub₁₂ : Ω₁ ⊆ Ω₂
  cpt : IsCompact (closure Ω₂)
  κ : ℝ
  κ_pos : 0 < κ
  incl₀ : ∀ y ∈ Ω₀, closedBall y (6 * κ) ⊆ Ω₁
  incl₁ : ∀ y ∈ Ω₁, closedBall y (6 * κ) ⊆ Ω₂
  C_D : ℝ
  one_lt_C_D : 1 < C_D
  doubling : ∀ x ∈ Ω₁, ∀ r : ℝ, 0 < r → r ≤ 3 * κ →
    0 < μ (ball x (2 * r)) ∧
      μ (ball x (2 * r)) ≤ ENNReal.ofReal C_D * μ (ball x r) ∧
      μ (ball x r) < ⊤
  noAtoms : ∀ x : X, μ {x} = 0
  finΩ₂ : μ Ω₂ < ⊤

/-- Optional measurable, symmetric truncation distance, comparable on Ω₁. Joint measurability is part of the structure (BB Theorem 7.12, p. 301). -/
structure TruncDist {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
    (S : LocDoubling X) where
  d' : X → X → ℝ
  θ₁ : ℝ
  θ₂ : ℝ
  θ₁_pos : 0 < θ₁
  θ₁_le : θ₁ ≤ θ₂
  comp : ∀ x ∈ S.Ω₁, ∀ y ∈ S.Ω₁,
    θ₁ * dist x y ≤ d' x y ∧ d' x y ≤ θ₂ * dist x y
  meas : Measurable (Function.uncurry d')
  symm : ∀ x y, d' x y = d' y x

/-- A doubling patch (P1–P5), including finite outer measure, compact centre
closure and absence of atoms. The parameter sets need not be open. -/
structure DoublingPatch (X : Type*) [MetricSpace X] [MeasurableSpace X] [BorelSpace X] where
  μ : Measure X
  S : Set X
  W : Set X
  ρ : ℝ
  C_D : ℝ
  ρ_pos : 0 < ρ
  one_lt_C_D : 1 < C_D
  incl : ∀ z ∈ S, ball z (6 * ρ) ⊆ W
  doubling : ∀ z ∈ S, ∀ s : ℝ, 0 < s → s ≤ 6 * ρ →
    0 < μ (ball z s) ∧ μ (ball z s) < ⊤ ∧
      μ (ball z s) ≤ ENNReal.ofReal C_D * μ (ball z (s / 2))
  measurable_W : MeasurableSet W
  finite_W : μ W < ⊤
  compact_closure : IsCompact (closure S)
  noAtoms : ∀ x : X, μ {x} = 0

/-- The volume function used away from the diagonal (BB p. 295).
Its total extension has value zero on the diagonal; kernels exclude that null point. -/
def volumeAt {X : Type*} [MetricSpace X] [MeasurableSpace X]
    (μ : Measure X) (x y : X) : ℝ≥0∞ := μ (ball x (dist x y))

end RothschildStein.H2
