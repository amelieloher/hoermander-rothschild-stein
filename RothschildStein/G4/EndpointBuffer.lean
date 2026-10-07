-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.G1.FlowComposition

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set

namespace RothschildStein.G4

/-- Reversing from the actual time-one endpoint recovers the original
trajectory on [0,1], on the stated finite local overlap
(BB Lemma 9.48, pp. 441–442). -/
theorem localFlow_endpoint_reverse {N : ℕ} {Ω U : Set (Fin N → ℝ)}
    (hΩ : IsOpen Ω) (Z : (Fin N → ℝ) → (Fin N → ℝ))
    (hZ : ContDiffOn ℝ (⊤ : ℕ∞) Z Ω) {τ : ℝ} (hτ : 1 < τ)
    (Φ : ((Fin N → ℝ) × ℝ) → (Fin N → ℝ))
    (hΦ : ∀ x ∈ U, Φ (x, 0) = x ∧ ∀ v ∈ Ioo (-τ) τ,
      HasDerivAt (fun w => Φ (x, w)) (Z (Φ (x, v))) v ∧ Φ (x, v) ∈ Ω)
    {x : Fin N → ℝ} (hx : x ∈ U) (hend : Φ (x, 1) ∈ U)
    {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) :
    Φ (Φ (x, 1), -s) = Φ (x, 1 - s) := by
  have hτ₀ : 0 < τ := lt_trans zero_lt_one hτ
  have ht₁ : (1 : ℝ) ∈ Ioo (-τ) τ := ⟨by linarith, hτ⟩
  have hneg : -s ∈ Ioo (-τ) τ := ⟨by linarith [hs.2], by linarith [hs.1]⟩
  have hsum : -s + 1 ∈ Ioo (-τ) τ := ⟨by linarith [hs.2], by linarith [hs.1]⟩
  have hh := RothschildStein.G1.localFlow_composition hΩ hZ hτ₀ Φ hΦ hx ht₁ hneg hsum hend
  have he : -s + 1 = 1 - s := by ring
  simpa only [he] using hh

end RothschildStein.G4
