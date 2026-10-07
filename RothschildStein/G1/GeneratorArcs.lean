-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.G1.GeneratorCosts
public import Mathlib.Logic.Relation

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set
open scoped ENNReal

namespace RothschildStein.G1

/-- A normalized C¹ arc of one original generator, with signed
constant elapsed time and all intermediate points in the stated domain
(BB Theorem 1.45, pp. 25–26, 34). -/
def IsGeneratorArc {m n : ℕ} (Ω : Set (Fin n → ℝ))
    (X : Fin m → (Fin n → ℝ) → (Fin n → ℝ)) (x y : Fin n → ℝ) : Prop :=
  ∃ (i : Fin m) (c : ℝ) (γ : ℝ → Fin n → ℝ),
    ContDiffOn ℝ 1 γ (Icc 0 1) ∧ MapsTo γ (Icc 0 1) Ω ∧
    (∀ t ∈ Icc 0 1, HasDerivAt γ (c • X i (γ t)) t) ∧ γ 0 = x ∧ γ 1 = y

/-- Finite generator reachability is the finite equivalence closure
of actual generator arcs. Reversed arcs correspond to signed elapsed time
(BB Theorem 1.45, p. 34). -/
def FiniteGeneratorPath {m n : ℕ} (Ω : Set (Fin n → ℝ))
    (X : Fin m → (Fin n → ℝ) → (Fin n → ℝ)) :
    (Fin n → ℝ) → (Fin n → ℝ) → Prop := Relation.EqvGen (IsGeneratorArc Ω X)

/-- Both endpoints of an actual generator arc lie in its domain
(BB Theorem 1.45, p. 34). -/
theorem IsGeneratorArc.endpoints_mem {m n : ℕ} {Ω : Set (Fin n → ℝ)}
    {X : Fin m → (Fin n → ℝ) → (Fin n → ℝ)} {x y : Fin n → ℝ}
    (h : IsGeneratorArc Ω X x y) : x ∈ Ω ∧ y ∈ Ω := by
  obtain ⟨i, c, γ, hs, hrange, hd, h0, h1⟩ := h
  exact ⟨h0 ▸ hrange (by norm_num), h1 ▸ hrange (by norm_num)⟩

/-- An actual generator arc has finite weighted control distance
for every positive generator weight (BB Theorem 1.45, p. 34). -/
theorem IsGeneratorArc.controlDistance_ne_top {m n : ℕ} {Ω : Set (Fin n → ℝ)}
    {X : Fin m → (Fin n → ℝ) → (Fin n → ℝ)} (w : Fin m → ℕ+)
    {x y : Fin n → ℝ} (h : IsGeneratorArc Ω X x y) :
    controlDistance Ω w X x y ≠ ∞ := by
  obtain ⟨i, c, γ, hs, hrange, hd, h0, h1⟩ := h
  let δ : ℝ := |c| + 1
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hcost : |c| ≤ δ ^ (w i : ℕ) :=
    (show |c| ≤ δ by dsimp [δ]; linarith).trans
      (le_self_pow₀ (show 1 ≤ δ by dsimp [δ]; linarith [abs_nonneg c]) (w i).ne_zero)
  have hγ := isControlledCurve_generatorArc hs hrange i hδ hd hcost
  have hh := controlDistance_le_of_curve hγ
  rw [h0, h1] at hh
  exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top hh

end RothschildStein.G1
