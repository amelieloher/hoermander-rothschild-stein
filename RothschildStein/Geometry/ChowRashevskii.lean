-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module
public import Mathlib
public import RothschildStein.Definitions.bracketSpansOn
public import RothschildStein.Definitions.controlDistance
public import RothschildStein.G1.ChowConnectivity
set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
open Set MeasureTheory
open scoped BigOperators ENNReal
namespace RothschildStein.Geometry

/-- Revised A: original-generator connectivity, weighted finiteness
and C¹ constancy (BB Thm 1.45, pp. 25–26, 34; Prop. 1.28, p. 17). -/

theorem chow_rashevskii
    {m n : ℕ} {Ω : Set (Fin n → ℝ)} (hΩ : IsOpen Ω)
    (hconn : IsPreconnected Ω)
    (X : Fin m → (Fin n → ℝ) → (Fin n → ℝ))
    (hX : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (X i) Ω)
    (hrank : bracketSpansOn Ω X) :
    let arc : Set (Fin n → ℝ) → (Fin n → ℝ) → (Fin n → ℝ) → Prop :=
      fun D a b => ∃ (i : Fin m) (c : ℝ) (γ : ℝ → Fin n → ℝ),
        ContDiffOn ℝ 1 γ (Icc 0 1) ∧ MapsTo γ (Icc 0 1) D ∧
        (∀ t ∈ Icc (0 : ℝ) 1, HasDerivAt γ (c • X i (γ t)) t) ∧
        γ 0 = a ∧ γ 1 = b
    (∀ x ∈ Ω, ∀ W : Set (Fin n → ℝ), IsOpen W → x ∈ W → W ⊆ Ω →
      ∃ U : Set (Fin n → ℝ), IsOpen U ∧ x ∈ U ∧ U ⊆ W ∧
        ∀ a ∈ U, ∀ b ∈ U, Relation.EqvGen (arc W) a b) ∧
    (∀ x ∈ Ω, ∀ y ∈ Ω, Relation.EqvGen (arc Ω) x y) ∧
    (∀ w : Fin m → ℕ+, ∀ x ∈ Ω, ∀ y ∈ Ω, controlDistance Ω w X x y ≠ ∞) ∧
    (∀ f : (Fin n → ℝ) → ℝ, ContDiffOn ℝ 1 f Ω →
      (∀ z ∈ Ω, ∀ i, fderiv ℝ f z (X i z) = 0) →
      ∀ x ∈ Ω, ∀ y ∈ Ω, f y = f x) := by
  intro arc
  exact ⟨fun x hx W hW hxW hWΩ =>
      G1.exists_local_generator_connectivity_of_bracketSpansOn hΩ X hX hrank x hx W hW hxW hWΩ,
    fun x hx y hy => G1.finite_generator_connectivity_of_bracketSpansOn hΩ hconn X hX hrank hx hy,
    fun w x hx y hy => G1.controlDistance_ne_top_of_bracketSpansOn hΩ hconn w X hX hrank hx hy,
    fun f hf hzero x hx y hy => G1.constancy_of_bracketSpansOn hΩ hconn X hX hrank hf hzero hx hy⟩
end RothschildStein.Geometry
