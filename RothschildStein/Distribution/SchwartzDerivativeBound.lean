-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.Distribution.WeightedSchwartzMoment

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
open MeasureTheory SchwartzMap
open scoped FourierTransform
namespace RothschildStein.Distribution

/-- pointwise derivatives of every complex Schwartz
test are bounded by the exact source Sobolev norm at order n+s. -/
theorem norm_iteratedFDeriv_le_sobolev {N : ℕ} (n : ℕ) (s : ℝ)
    (hs : (N : ℝ) < 2 * s) (φ : 𝓢(Hormander.A.Carrier N, ℂ)) (x : Hormander.A.Carrier N) :
    ‖iteratedFDeriv ℝ n φ x‖ ≤ (2 * Real.pi) ^ n *
      ‖(Hormander.A.memLp_bessel_weight hs).toLp
        (fun ξ : Hormander.A.Carrier N => (1 + ‖ξ‖ ^ 2) ^ (-s / 2))‖ *
      ‖Hormander.A.schwartzToSobolev ((n : ℝ) + s) φ‖ := by
  have hi (m : ℕ) (_hm : (m : ℕ∞) ≤ (⊤ : ℕ∞)) :
      Integrable (fun ξ => ‖ξ‖ ^ m * ‖(𝓕 φ : 𝓢(Hormander.A.Carrier N, ℂ)) ξ‖) volume :=
    (𝓕 φ : 𝓢(Hormander.A.Carrier N, ℂ)).integrable_pow_mul volume m
  have h := Hormander.A.norm_iteratedFDeriv_fourierInv_le hi
    (𝓕 φ : 𝓢(Hormander.A.Carrier N, ℂ)).continuous.aestronglyMeasurable
    (show (n : ℕ∞) ≤ (⊤ : ℕ∞) from le_top) x
  have he : 𝓕⁻ ((𝓕 φ : 𝓢(Hormander.A.Carrier N, ℂ)) : Hormander.A.Carrier N → ℂ) =
      (φ : Hormander.A.Carrier N → ℂ) := by
    rw [← SchwartzMap.fourierInv_coe]
    simp
  rw [he] at h
  exact h.trans ((mul_le_mul_of_nonneg_left (integral_fourier_moment_le n s hs φ)
    (by positivity)).trans_eq (mul_assoc _ _ _).symm)

end RothschildStein.Distribution
