-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.S.ClassicalWords

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
open Set TopologicalSpace
namespace RothschildStein.S
variable {n : ℕ}

/-- A compact smooth test has a bounded field derivative
on the entire open domain, even when the field is only locally smooth.
The derivative vanishes off the test support (BB Prop 2.22, p. 89). -/
theorem exists_uniform_compact_test_field_derivative_bound
    (Ω : Opens (Fin n → ℝ)) (K : Compacts (Fin n → ℝ))
    (hKΩ : (K : Set (Fin n → ℝ)) ⊆ Ω)
    (X : (Fin n → ℝ) → (Fin n → ℝ))
    (hX : ContDiffOn ℝ (⊤ : ℕ∞) X (Ω : Set (Fin n → ℝ)))
    (φ : (Fin n → ℝ) → ℝ) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hs : tsupport φ ⊆ K) :
    ∃ A : ℝ,0 ≤ A ∧ ∀ x ∈ (Ω : Set (Fin n → ℝ)),|fieldDerivative X φ x| ≤ A := by
  have hc := (contDiffOn_fieldDerivative Ω X φ hX hφ.contDiffOn).continuousOn
  obtain ⟨A,hA⟩ := K.isCompact.exists_bound_of_continuousOn (hc.mono hKΩ)
  refine ⟨max A 0,le_max_right A 0,?_⟩
  intro x _
  by_cases hx : x ∈ (K : Set (Fin n → ℝ))
  · simpa only [Real.norm_eq_abs] using (hA x hx).trans (le_max_left A 0)
  · have hz : fieldDerivative X φ x = 0 := image_eq_zero_of_notMem_tsupport
      (fun hy => hx (hs (tsupport_fieldDerivative_subset X φ hy)))
    simpa only [hz,abs_zero] using le_max_right A 0

end RothschildStein.S
