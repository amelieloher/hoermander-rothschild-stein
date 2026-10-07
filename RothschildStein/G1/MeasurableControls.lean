-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.G1.ControlledBasics

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set Filter MeasureTheory
open scoped BigOperators

namespace RothschildStein.G1

/-- Controls have globally measurable representatives, equal to the
original controls almost everywhere on the fixed time interval. This is used
in weighted piecewise concatenation (BB Def 1.38, p. 21). -/
theorem isControlledCurve_measurable_controls {m n : ℕ} {Ω : Set (Fin n → ℝ)}
    {w : Fin m → ℕ+} {X : Fin m → (Fin n → ℝ) → (Fin n → ℝ)}
    {δ : ℝ} {γ : ℝ → (Fin n → ℝ)} (hγ : isControlledCurve Ω w X δ γ) :
    ∃ a : Fin m → ℝ → ℝ, (∀ i, Measurable (a i)) ∧
      ∀ᵐ t ∂(volume.restrict (Icc (0 : ℝ) 1)),
        (∀ i, |a i t| ≤ δ ^ (w i : ℕ)) ∧
        HasDerivAt γ (∑ i, a i t • X i (γ t)) t := by
  obtain ⟨a, hmeas, ha⟩ := hγ.2.2.2
  refine ⟨fun i => (hmeas i).mk (a i), fun i => (hmeas i).measurable_mk, ?_⟩
  have heq : ∀ᵐ t ∂(volume.restrict (Icc (0 : ℝ) 1)), ∀ i, a i t = (hmeas i).mk (a i) t :=
    ae_all_iff.mpr (fun i => (hmeas i).ae_eq_mk)
  filter_upwards [ha, heq] with t ht he
  simpa only [← he] using ht

end RothschildStein.G1
