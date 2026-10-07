-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module
public import RothschildStein.G4.ConstantControl
@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set MeasureTheory
open scoped BigOperators ENNReal
namespace RothschildStein.G4

/-- Zero coefficients give an actual constant-control curve at every
positive radius. -/
theorem isConstantControlledCurve_const {m n : ℕ} {Ω : Set (Fin n → ℝ)}
    (w : Fin m → ℕ+) (Z : Fin m → (Fin n → ℝ) → (Fin n → ℝ))
    {δ : ℝ} (hδ : 0 < δ) {x : Fin n → ℝ} (hx : x ∈ Ω) :
    IsConstantControlledCurve Ω w Z δ (fun _ => x) := by
  refine ⟨hδ,(LipschitzWith.const x).lipschitzOnWith.absolutelyContinuousOnInterval,fun _ _ => hx,0,?_,?_⟩
  · intro i
    simp only [Pi.zero_apply,abs_zero]
    exact (pow_pos hδ _).le
  · exact Filter.Eventually.of_forall (fun t => by simpa using hasDerivAt_const t x)

/-- Constant-control cost at a domain point is zero, without rank or
connectivity assumptions. -/
theorem constantControlDistance_self {m n : ℕ} {Ω : Set (Fin n → ℝ)}
    (w : Fin m → ℕ+) (Z : Fin m → (Fin n → ℝ) → (Fin n → ℝ))
    {x : Fin n → ℝ} (hx : x ∈ Ω) : constantControlDistance Ω w Z x x = 0 := by
  apply le_antisymm _ bot_le
  by_contra h
  have hpos : 0 < constantControlDistance Ω w Z x x := lt_of_not_ge h
  obtain ⟨δ,_hδ,hδpos,hlt⟩ := ENNReal.lt_iff_exists_real_btwn.mp hpos
  have hcost : constantControlDistance Ω w Z x x ≤ ENNReal.ofReal δ :=
    sInf_le ⟨δ,rfl,(fun _ => x),isConstantControlledCurve_const w Z
      (ENNReal.ofReal_pos.mp hδpos) hx,rfl,rfl⟩
  exact (not_lt_of_ge hcost) hlt
end RothschildStein.G4
