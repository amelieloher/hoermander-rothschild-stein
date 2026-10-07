-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H3.HomogeneousBounds
public import RothschildStein.H3.HomogeneousOperators
public import RothschildStein.G2.LocalPower
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
open Set MeasureTheory
namespace RothschildStein.H3
open G2
variable {N : ℕ} {G : HomogeneousGroup N}

/-- A positive-type kernel has precisely the punctured smoothness
and degree α−Q of BB Definition 8.13, p. 346. -/
structure PositiveType (G : HomogeneousGroup N) (α : ℝ)
    (T : (Fin N → ℝ) → ℝ) : Prop where
  positive : 0 < α
  smooth : ContDiffOn ℝ (⊤ : ℕ∞) T {0}ᶜ
  homogeneous : ∀ t : ℝ, 0 < t → ∀ x, x ≠ 0 →
    T (G.dilate t x) = t ^ (α - (G.homogeneousDimension : ℝ)) * T x

/-- The type kernel is strongly measurable, including its arbitrary
value at the origin (BB Definition 8.13, p. 346). -/
theorem PositiveType.stronglyMeasurable {α : ℝ} {T : (Fin N → ℝ) → ℝ}
    (hT : PositiveType G α T) : StronglyMeasurable T :=
  hT.smooth.continuousOn.stronglyMeasurable_of_countable_compl (by simp)

/-- The actual maximum on a gauge unit sphere bounds a type kernel
by the corresponding homogeneous power (BB (8.7), p. 346). -/
theorem PositiveType.sphere_bound {α : ℝ} {T ν : (Fin N → ℝ) → ℝ}
    (hT : PositiveType G α T) (hν : G.IsHomogeneousGauge ν) :
    ∃ Λ : ℝ, 0 ≤ Λ ∧ (∃ z, ν z = 1 ∧ |T z| = Λ) ∧
      (∀ z, ν z = 1 → |T z| ≤ Λ) ∧
      ∀ x, x ≠ 0 → |T x| ≤ Λ * (ν x) ^ (α - (G.homogeneousDimension : ℝ)) :=
  homogeneous_function_sphere_bound hν _ hT.smooth.continuousOn hT.homogeneous

end RothschildStein.H3
