-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.G1.ControlSeparation
public import RothschildStein.G1.WeightedSubcurves

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set
open scoped BigOperators

namespace RothschildStein.G1

/-- A small actual control parameter prevents every intermediate
point from leaving a bounded-field buffer. The proof uses first exit rather
than a global bound on the fields (BB Props 1.37/1.42, pp. 20–24). -/
theorem controlledCurve_stays_in_buffer {m n : ℕ} {Ω : Set (Fin n → ℝ)}
    {w : Fin m → ℕ+} {X : Fin m → (Fin n → ℝ) → (Fin n → ℝ)}
    (hw : ∀ i, (w i : ℕ) ≤ 2) {δ B R : ℝ} {γ : ℝ → (Fin n → ℝ)}
    (hγ : isControlledCurve Ω w X δ γ) (hδ1 : δ ≤ 1) (hB : 0 ≤ B) (hR : 0 < R)
    (hsmall : δ * B < R)
    (hbound : ∀ z, ‖z - γ 0‖ ≤ R → ∑ i, ‖X i z‖ ≤ B) :
    ∀ t ∈ Icc (0 : ℝ) 1, ‖γ t - γ 0‖ < R := by
  intro t ht
  rcases eq_or_lt_of_le ht.1 with heq | hpos
  · rw [← heq, sub_self, norm_zero]; exact hR
  · by_contra hbad
    have hsqrt : Real.sqrt t ≤ 1 := Real.sqrt_le_one.mpr ht.2
    have hparam : Real.sqrt t * δ ≤ δ := by nlinarith [hγ.1]
    have hc := isControlledCurve_subcurve hw hγ le_rfl hpos ht.2
    simp only [sub_zero, zero_add] at hc
    have hm := controlledCurve_firstExit_bound hc (hparam.trans hδ1) hB hR
      (by simpa only [mul_zero, add_zero, mul_one, zero_add] using le_of_not_gt hbad)
      (by simpa only [mul_zero, add_zero] using hbound)
    exact (not_le_of_gt hsmall) (hm.trans (mul_le_mul_of_nonneg_right hparam hB))

/-- Small-parameter endpoint displacement uses only the local
buffer coefficient bound, after first exit is excluded
(BB Props 1.37/1.42, pp. 20–24). -/
theorem controlledCurve_endpoint_displacement_le {m n : ℕ} {Ω : Set (Fin n → ℝ)}
    {w : Fin m → ℕ+} {X : Fin m → (Fin n → ℝ) → (Fin n → ℝ)}
    (hw : ∀ i, (w i : ℕ) ≤ 2) {δ B R : ℝ} {γ : ℝ → (Fin n → ℝ)}
    (hγ : isControlledCurve Ω w X δ γ) (hδ1 : δ ≤ 1) (hB : 0 ≤ B) (hR : 0 < R)
    (hsmall : δ * B < R)
    (hbound : ∀ z, ‖z - γ 0‖ ≤ R → ∑ i, ‖X i z‖ ≤ B) :
    ‖γ 1 - γ 0‖ ≤ δ * B := by
  have hstay := controlledCurve_stays_in_buffer hw hγ hδ1 hB hR hsmall hbound
  simpa only [mul_one] using controlledCurve_initial_displacement_le hγ hδ1 hB
    (show (1 : ℝ) ∈ Icc 0 1 from ⟨zero_le_one, le_rfl⟩)
    (fun t ht => hbound _ (hstay t ht).le)

end RothschildStein.G1
