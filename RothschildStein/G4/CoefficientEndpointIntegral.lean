-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.G4.LinearFieldFlowIntegral
public import RothschildStein.G4.TransportedSmoothness

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set MeasureTheory
open scoped BigOperators

namespace RothschildStein.G4

/-- The actual coefficient derivative is the integral of transported
fields evaluated at the fixed endpoint, using actual local flow composition
(BB Lemma 9.48, pp. 441–442). -/
theorem linear_field_flow_coefficient_endpoint_integral {m n : ℕ}
    {A : Set (Fin m → ℝ)} {Ω U : Set (Fin n → ℝ)}
    (hA : IsOpen A) (hΩ : IsOpen Ω) (hU : IsOpen U) (hUΩ : U ⊆ Ω)
    (W : Fin m → (Fin n → ℝ) → (Fin n → ℝ))
    (hW : ∀ j, ContDiffOn ℝ (⊤ : ℕ∞) (W j) Ω)
    {τ : ℝ} (hτ : 1 < τ) (Φ : (((Fin m → ℝ) × (Fin n → ℝ)) × ℝ) → (Fin n → ℝ))
    (hc : ContinuousOn Φ ((A ×ˢ U) ×ˢ Ioo (-τ) τ))
    (hΦ : ∀ p ∈ A ×ˢ U, Φ (p, 0) = p.2 ∧ ∀ s ∈ Ioo (-τ) τ,
      HasDerivAt (fun v => Φ (p, v)) (∑ j, p.1 j • W j (Φ (p, s))) s ∧ Φ (p, s) ∈ Ω)
    {z : Fin m → ℝ} (hz : z ∈ A) {x : Fin n → ℝ} (hx : x ∈ U)
    (hend : ∀ s ∈ Icc (0 : ℝ) 1, Φ ((z, x), s) ∈ U) (i : Fin m) :
    fderiv ℝ (fun z' => Φ ((z', x), 1)) z (Pi.single i 1) = ∫ s in 0..1,
      fderiv ℝ (fun y => Φ ((z, y), s)) (Φ ((z, Φ ((z, x), 1)), -s))
        (W i (Φ ((z, Φ ((z, x), 1)), -s))) := by
  have hτ₀ : 0 < τ := lt_trans zero_lt_one hτ
  have ht₁ : (1 : ℝ) ∈ Ioo (-τ) τ := ⟨by linarith, hτ⟩
  let Z : (Fin n → ℝ) → Fin n → ℝ := fun y => ∑ j, z j • W j y
  let θ : ((Fin n → ℝ) × ℝ) → Fin n → ℝ := fun p => Φ ((z, p.1), p.2)
  let y := θ (x, 1)
  let Q : ℝ → Fin n → ℝ := fun s => fderiv ℝ (fun v => θ (v, s)) (θ (y, -s)) (W i (θ (y, -s)))
  have hZ : ContDiffOn ℝ (⊤ : ℕ∞) Z Ω := linear_field_combination_contDiffOn W hW z
  have hsol : ∀ v ∈ U, θ (v, 0) = v ∧ ∀ s ∈ Ioo (-τ) τ,
      HasDerivAt (fun r => θ (v, r)) (Z (θ (v, s))) s ∧ θ (v, s) ∈ Ω :=
    fun v hv => hΦ (z, v) ⟨hz, hv⟩
  rw [linear_field_flow_coefficient_integral hA hΩ hU hUΩ W hW hτ₀ Φ hc hΦ hz hx ht₁
    (by simpa only [uIcc_of_le zero_le_one] using hend) i]
  calc
    _ = ∫ s in (0 : ℝ)..1, Q (1 - s) := by
      apply intervalIntegral.integral_congr
      intro s hs
      have hs' : s ∈ Icc (0 : ℝ) 1 := by simpa only [uIcc_of_le zero_le_one] using hs
      have hsm : s - 1 ∈ Ioo (-τ) τ := ⟨by linarith [hs'.1], by linarith [hs'.2]⟩
      have hst : s - 1 + 1 ∈ Ioo (-τ) τ := ⟨by linarith [hs'.1], by linarith [hs'.2]⟩
      have hp := RothschildStein.G1.localFlow_composition hΩ hZ hτ₀ θ hsol hx ht₁ hsm hst
        (hend 1 (by simp))
      have he : θ (y, -(1 - s)) = θ (x, s) := by
        simpa only [y, sub_add_cancel, neg_sub, zero_sub] using hp
      change _ = (fderiv ℝ (fun v => θ (v, 1 - s)) (θ (y, -(1 - s)))) (W i (θ (y, -(1 - s))))
      rw [he]
    _ = ∫ s in (0 : ℝ)..1, Q s := by
      simpa only [sub_self, sub_zero] using intervalIntegral.integral_comp_sub_left (a := 0) (b := 1) Q 1

end RothschildStein.G4
