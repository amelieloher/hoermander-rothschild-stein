-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.G1.LinearFieldCoefficientOrigin
public import Mathlib.LinearAlgebra.Pi

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set
open scoped BigOperators
namespace RothschildStein.G1

/-- The genuine coefficient derivative evaluates arbitrary
coefficient directions by the corresponding vector-field combination. -/
theorem linear_field_timeOne_coefficient_apply {m n : ℕ}
    {A : Set (Fin m → ℝ)} {Ω U : Set (Fin n → ℝ)}
    (hA : IsOpen A) (hΩ : IsOpen Ω) (hU : IsOpen U) (hUΩ : U ⊆ Ω)
    (W : Fin m → (Fin n → ℝ) → (Fin n → ℝ))
    (hW : ∀ j, ContDiffOn ℝ (⊤ : ℕ∞) (W j) Ω)
    (hz : (0 : Fin m → ℝ) ∈ A) {τ : ℝ} (hτ : 1 < τ)
    (Φ : (((Fin m → ℝ) × (Fin n → ℝ)) × ℝ) → (Fin n → ℝ))
    (hc : ContinuousOn Φ ((A ×ˢ U) ×ˢ Ioo (-τ) τ))
    (hΦ : ∀ p ∈ A ×ˢ U, Φ (p, 0) = p.2 ∧ ∀ t ∈ Ioo (-τ) τ,
      HasDerivAt (fun v => Φ (p, v))
        (∑ j, p.1 j • W j (Φ (p, t))) t ∧ Φ (p, t) ∈ Ω)
    {x : Fin n → ℝ} (hx : x ∈ U) (v : Fin m → ℝ) :
    fderiv ℝ (fun z => Φ ((z, x), 1)) 0 v = ∑ i, v i • W i x := by
  classical
  have hv : v = ∑ i, v i • Pi.single i (1 : ℝ) := by
    ext j
    simp [Pi.single_apply]
  calc
    _ = (fderiv ℝ (fun z => Φ ((z, x), 1)) 0)
        (∑ i, v i • Pi.single i (1 : ℝ)) := congrArg _ hv
    _ = ∑ i, v i • ((fderiv ℝ (fun z => Φ ((z, x), 1)) 0) (Pi.single i 1)) := by
      rw [map_sum]
      apply Finset.sum_congr rfl
      intro i _
      exact map_smul _ _ _
    _ = _ := by
      apply Finset.sum_congr rfl
      intro i _
      rw [linear_field_timeOne_coefficient_origin hA hΩ hU hUΩ W hW hz hτ Φ hc hΦ hx i]

end RothschildStein.G1
