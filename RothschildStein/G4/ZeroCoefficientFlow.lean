-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.G4.CoefficientEndpointAgreement

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set
open scoped BigOperators

namespace RothschildStein.G4

/-- The actual coefficient flow with all coefficients zero is the
initial point throughout its local time interval (BB Lemma 9.48, pp. 441–443). -/
theorem linear_field_flow_zero_coefficients {m N : ℕ}
    {A : Set (Fin m → ℝ)} {Ω U : Set (Fin N → ℝ)}
    (W : Fin m → (Fin N → ℝ) → (Fin N → ℝ)) {τ : ℝ} (hτ : 0 < τ)
    (Φ : (((Fin m → ℝ) × (Fin N → ℝ)) × ℝ) → (Fin N → ℝ))
    (hΦ : ∀ p ∈ A ×ˢ U, Φ (p, 0) = p.2 ∧ ∀ v ∈ Ioo (-τ) τ,
      HasDerivAt (fun w => Φ (p, w)) (∑ j, p.1 j • W j (Φ (p, v))) v ∧ Φ (p, v) ∈ Ω)
    (hz : (0 : Fin m → ℝ) ∈ A) {x : Fin N → ℝ} (hx : x ∈ U)
    {t : ℝ} (ht : t ∈ Ioo (-τ) τ) : Φ ((0, x), t) = x := by
  have hzero : (0 : ℝ) ∈ Ioo (-τ) τ := ⟨by linarith, hτ⟩
  have hsub : uIcc 0 t ⊆ Ioo (-τ) τ := ordConnected_Ioo.uIcc_subset hzero ht
  have hd : ∀ v ∈ uIcc 0 t, HasDerivWithinAt (fun w => Φ ((0, x), w)) 0 (uIcc 0 t) v := by
    intro v hv
    simpa only [Pi.zero_apply, zero_smul, Finset.sum_const_zero] using
      ((hΦ (0, x) ⟨hz, hx⟩).2 v (hsub hv)).1.hasDerivWithinAt
  have hh := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le (C := 0) hd
    (fun v hv => by simp) (convex_uIcc (0 : ℝ) t) left_mem_uIcc right_mem_uIcc
  have hn : ‖Φ ((0, x), t) - x‖ ≤ 0 := by
    simpa only [(hΦ (0, x) ⟨hz, hx⟩).1, zero_mul] using hh
  exact sub_eq_zero.mp (norm_eq_zero.mp (le_antisymm hn (norm_nonneg _)))

end RothschildStein.G4
