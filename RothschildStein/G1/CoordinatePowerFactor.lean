-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.G1.ScalarPowerFactor

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

namespace RothschildStein.G1

/-- Scalar-time flatness of each coordinate gives a jointly
smooth vector power factor. This supplies the actual vector factors for
signed weighted commutator charts (BB Proposition 1.50, pp. 28–29). -/
theorem exists_smooth_coordinate_power_factor {E : Type} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [LocallyCompactSpace E] {N : ℕ}
    (k : ℕ) (G : E × ℝ → (Fin N → ℝ)) (hG : ContDiff ℝ (⊤ : ℕ∞) G)
    (hzero : ∀ x, ∀ j < k, ∀ i : Fin N,
      iteratedDeriv j (fun t => G (x, t) i) 0 = 0) :
    ∃ H : E × ℝ → (Fin N → ℝ), ContDiff ℝ (⊤ : ℕ∞) H ∧
      ∀ x t, G (x, t) = t ^ k • H (x, t) := by
  classical
  have hex := fun i : Fin N => exists_smooth_scalar_power_factor k
    (fun q => G q i) ((contDiff_apply ℝ ℝ i).comp hG)
    (fun x j hj => hzero x j hj i)
  choose H hH he using hex
  refine ⟨fun q i => H i q, contDiff_pi.mpr hH, ?_⟩
  intro x t
  funext i
  exact he i x t

end RothschildStein.G1
