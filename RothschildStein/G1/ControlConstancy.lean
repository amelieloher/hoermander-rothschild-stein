-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.G1.ControlledVariation

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set
open scoped BigOperators ENNReal

namespace RothschildStein.G1

/-- A C¹ function annihilated by every generator is constant
along every actual controlled curve. No bracket derivatives of the function
are required (BB Prop 1.28, p. 17). -/
theorem controlledCurve_constancy {m n : ℕ} {Ω : Set (Fin n → ℝ)}
    (hΩ : IsOpen Ω) {w : Fin m → ℕ+}
    {X : Fin m → (Fin n → ℝ) → (Fin n → ℝ)}
    {f : (Fin n → ℝ) → ℝ} (hf : ContDiffOn ℝ 1 f Ω)
    (hzero : ∀ z ∈ Ω, ∀ i, fderiv ℝ f z (X i z) = 0)
    {δ : ℝ} {γ : ℝ → (Fin n → ℝ)} (hγ : isControlledCurve Ω w X δ γ) :
    f (γ 1) = f (γ 0) := by
  have h := controlledCurve_variation_le hΩ hf hγ (C := 0) (by
    intro t ht
    simp only [hzero _ (hγ.2.2.1 ht), abs_zero, mul_zero, Finset.sum_const_zero, le_refl])
  exact sub_eq_zero.mp (abs_nonpos_iff.mp h)

/-- C¹ constancy follows from the finite-distance conclusion of
Chow, including the drift generator among the annihilation hypotheses
(BB Prop 1.28, p. 17). -/
theorem constancy_of_finite_control_distance {m n : ℕ} {Ω : Set (Fin n → ℝ)}
    (hΩ : IsOpen Ω) {w : Fin m → ℕ+}
    {X : Fin m → (Fin n → ℝ) → (Fin n → ℝ)}
    {f : (Fin n → ℝ) → ℝ} (hf : ContDiffOn ℝ 1 f Ω)
    (hzero : ∀ z ∈ Ω, ∀ i, fderiv ℝ f z (X i z) = 0)
    {x y : Fin n → ℝ} (hfinite : controlDistance Ω w X x y ≠ ∞) : f y = f x := by
  obtain ⟨δ, _, _, γ, hγ, hγ0, hγ1⟩ := exists_controlledCurve_of_controlDistance_lt
    ((ENNReal.lt_ofReal_iff_toReal_lt hfinite).mpr
      (show (controlDistance Ω w X x y).toReal < (controlDistance Ω w X x y).toReal + 1 by linarith))
  simpa only [hγ0, hγ1] using controlledCurve_constancy hΩ hf hzero hγ

end RothschildStein.G1
