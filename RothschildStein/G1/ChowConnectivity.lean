-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module
public import RothschildStein.G1.LocalGeneratorConnectivity
public import RothschildStein.G1.ActualControlComparison
public import RothschildStein.G1.ControlEuclideanContinuity
@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set
open scoped ENNReal
namespace RothschildStein.G1

/-- Pointwise Hörmander rank on a connected open domain gives
finite original-generator connectivity (BB Theorem 1.45, p. 34). -/
theorem finite_generator_connectivity_of_bracketSpansOn {m n : ℕ}
    {Ω : Set (Fin n → ℝ)} (hΩ : IsOpen Ω) (hconn : IsPreconnected Ω)
    (X : Fin m → (Fin n → ℝ) → (Fin n → ℝ))
    (hX : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (X i) Ω) (hrank : bracketSpansOn Ω X)
    {x y : Fin n → ℝ} (hx : x ∈ Ω) (hy : y ∈ Ω) : FiniteGeneratorPath Ω X x y :=
  finite_generator_connectivity_of_local_connectivity hΩ hconn X
    (exists_local_generator_connectivity_of_bracketSpansOn hΩ X hX hrank) hx hy

/-- The weighted control distance is finite for every
pair in a connected Hörmander domain, for arbitrary positive weights. -/
theorem controlDistance_ne_top_of_bracketSpansOn {m n : ℕ}
    {Ω : Set (Fin n → ℝ)} (hΩ : IsOpen Ω) (hconn : IsPreconnected Ω)
    (w : Fin m → ℕ+) (X : Fin m → (Fin n → ℝ) → (Fin n → ℝ))
    (hX : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (X i) Ω) (hrank : bracketSpansOn Ω X)
    {x y : Fin n → ℝ} (hx : x ∈ Ω) (hy : y ∈ Ω) : controlDistance Ω w X x y ≠ ∞ :=
  (finite_generator_connectivity_of_bracketSpansOn hΩ hconn X hX hrank hx hy).controlDistance_ne_top w hx

/-- A C¹ function annihilated by all original generators is
constant on the connected domain, including drift (BB p. 17). -/
theorem constancy_of_bracketSpansOn {m n : ℕ}
    {Ω : Set (Fin n → ℝ)} (hΩ : IsOpen Ω) (hconn : IsPreconnected Ω)
    (X : Fin m → (Fin n → ℝ) → (Fin n → ℝ))
    (hX : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (X i) Ω) (hrank : bracketSpansOn Ω X)
    {f : (Fin n → ℝ) → ℝ} (hf : ContDiffOn ℝ 1 f Ω)
    (hzero : ∀ z ∈ Ω, ∀ i, fderiv ℝ f z (X i z) = 0)
    {x y : Fin n → ℝ} (hx : x ∈ Ω) (hy : y ∈ Ω) : f y = f x :=
  constancy_of_finite_control_distance hΩ hf hzero
    (controlDistance_ne_top_of_bracketSpansOn hΩ hconn (fun _ => 1) X hX hrank hx hy)

end RothschildStein.G1
