-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H1.PotentialSmooth
public import Mathlib.MeasureTheory.Integral.Prod

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
open Set MeasureTheory
namespace RothschildStein.H1
variable {N : ℕ} (G : HomogeneousGroup N)

private theorem compact_test_bound {ψ : (Fin N → ℝ) → ℝ}
    (hψ : Continuous ψ) (hcψ : HasCompactSupport ψ) : ∃ B : ℝ, 0 ≤ B ∧ ∀ x, ‖ψ x‖ ≤ B := by
  obtain ⟨B, hB⟩ := hcψ.isCompact.exists_bound_of_continuousOn hψ.continuousOn
  refine ⟨max B 0, le_max_right _ _, fun x => ?_⟩
  by_cases hx : ψ x = 0
  · simpa only [hx, norm_zero] using le_max_right B 0
  · exact (hB x (subset_closure hx)).trans (le_max_left _ _)

private def pairingSupport (φ ψ : (Fin N → ℝ) → ℝ) : Set (Fin N → ℝ) :=
  (fun p : (Fin N → ℝ) × (Fin N → ℝ) => G.mul (G.inv p.1) p.2) ''
    (tsupport φ ×ˢ tsupport ψ)

private theorem pairingSupport_compact {φ ψ : (Fin N → ℝ) → ℝ}
    (hcφ : HasCompactSupport φ) (hcψ : HasCompactSupport ψ) :
    IsCompact (pairingSupport G φ ψ) := by
  have hi : Continuous (fun p : (Fin N → ℝ) × (Fin N → ℝ) => G.inv p.1) :=
    (G2.continuous_inv G).comp continuous_fst
  have hm : Continuous (fun p : (Fin N → ℝ) × (Fin N → ℝ) => G.mul (G.inv p.1) p.2) :=
    Continuous.comp (g := fun p : (Fin N → ℝ) × (Fin N → ℝ) => G.mul p.1 p.2)
      (f := fun p : (Fin N → ℝ) × (Fin N → ℝ) => (G.inv p.1, p.2))
      (G2.continuous_mul G) (hi.prodMk continuous_snd)
  exact (hcφ.isCompact.prod hcψ.isCompact).image hm

private theorem pairing_norm_bound {Γ φ ψ : (Fin N → ℝ) → ℝ} {B : ℝ}
    (hB0 : 0 ≤ B) (hB : ∀ x, ‖ψ x‖ ≤ B) (p : (Fin N → ℝ) × (Fin N → ℝ)) :
    ‖φ p.1 * Γ p.2 * ψ (G.mul p.1 p.2)‖ ≤
      |φ p.1| * |(pairingSupport G φ ψ).indicator Γ p.2| * B := by
  by_cases hpφ : φ p.1 = 0
  · simp [hpφ]
  by_cases hpψ : ψ (G.mul p.1 p.2) = 0
  · have hn : 0 ≤ |φ p.1| * |(pairingSupport G φ ψ).indicator Γ p.2| * B :=
      mul_nonneg (mul_nonneg (abs_nonneg _) (abs_nonneg _)) hB0
    simpa only [hpψ, mul_zero, norm_zero] using hn
  have hpK : p.2 ∈ pairingSupport G φ ψ := by
    refine ⟨(p.1, G.mul p.1 p.2), ⟨subset_closure hpφ, subset_closure hpψ⟩, ?_⟩
    simp only [← G2.mul_assoc, G2.inv_mul, G2.zero_mul]
  rw [Set.indicator_of_mem hpK, Real.norm_eq_abs, abs_mul, abs_mul]
  exact mul_le_mul_of_nonneg_left (by simpa only [Real.norm_eq_abs] using hB (G.mul p.1 p.2))
    (mul_nonneg (abs_nonneg _) (abs_nonneg _))

private theorem pairing_measurable {Γ φ ψ : (Fin N → ℝ) → ℝ}
    (hΓ : LocallyIntegrable Γ) (hφ : Continuous φ) (hψ : Continuous ψ) :
    AEStronglyMeasurable
      (fun p : (Fin N → ℝ) × (Fin N → ℝ) => φ p.1 * Γ p.2 * ψ (G.mul p.1 p.2))
      (volume.prod volume) := by
  have hmφ : AEStronglyMeasurable (fun p : (Fin N → ℝ) × (Fin N → ℝ) => φ p.1)
      (volume.prod volume) := hφ.aestronglyMeasurable.comp_fst
  have hmΓ : AEStronglyMeasurable (fun p : (Fin N → ℝ) × (Fin N → ℝ) => Γ p.2)
      (volume.prod volume) := hΓ.aestronglyMeasurable.comp_snd
  have hmψ : AEStronglyMeasurable (fun p : (Fin N → ℝ) × (Fin N → ℝ) => ψ (G.mul p.1 p.2))
      (volume.prod volume) := (hψ.comp (G2.continuous_mul G)).aestronglyMeasurable
  exact (hmφ.mul hmΓ).mul hmψ

private theorem integrable_pairing_translated {Γ φ ψ : (Fin N → ℝ) → ℝ}
    (hΓ : LocallyIntegrable Γ) (hφ : Continuous φ) (hcφ : HasCompactSupport φ)
    (hψ : Continuous ψ) (hcψ : HasCompactSupport ψ) :
    Integrable (fun p : (Fin N → ℝ) × (Fin N → ℝ) =>
      φ p.1 * Γ p.2 * ψ (G.mul p.1 p.2)) (volume.prod volume) := by
  let K := pairingSupport G φ ψ
  have hK := pairingSupport_compact G hcφ hcψ
  have hiΓ : Integrable (K.indicator Γ) :=
    (integrable_indicator_iff hK.measurableSet).mpr (hΓ.integrableOn_isCompact hK)
  have hiφ : Integrable φ := hφ.integrable_of_hasCompactSupport hcφ
  obtain ⟨B, hB0, hB⟩ := compact_test_bound hψ hcψ
  have hd : Integrable (fun p : (Fin N → ℝ) × (Fin N → ℝ) =>
      |φ p.1| * |K.indicator Γ p.2| * B) (volume.prod volume) :=
    (hiφ.abs.mul_prod hiΓ.abs).mul_const B
  exact Integrable.mono' hd (pairing_measurable G hΓ hφ hψ)
    (Filter.Eventually.of_forall (pairing_norm_bound G hB0 hB))

/-- Joint absolute convergence of the potential pairing
(BB p. 270). -/
theorem integrable_potential_pairing {Γ φ ψ : (Fin N → ℝ) → ℝ}
    (hΓ : LocallyIntegrable Γ) (hφ : Continuous φ) (hcφ : HasCompactSupport φ)
    (hψ : Continuous ψ) (hcψ : HasCompactSupport ψ) :
    Integrable (fun p : (Fin N → ℝ) × (Fin N → ℝ) =>
      φ p.1 * Γ (G.mul (G.inv p.1) p.2) * ψ p.2) (volume.prod volume) := by
  have hp := G2.measurePreserving_invLeftSkew G
  rw [Measure.volume_eq_prod] at hp
  have he := hp.integrable_comp_of_integrable (integrable_pairing_translated G hΓ hφ hcφ hψ hcψ)
  simpa only [Function.comp_def, ← G2.mul_assoc, G2.mul_inv, G2.zero_mul] using he

/-- Fubini for the actual group potential against a compact
continuous test, with absolute convergence proved above (BB p. 270). -/
theorem fundamentalPotential_pairing {Γ φ ψ : (Fin N → ℝ) → ℝ}
    (hΓ : LocallyIntegrable Γ) (hφ : Continuous φ) (hcφ : HasCompactSupport φ)
    (hψ : Continuous ψ) (hcψ : HasCompactSupport ψ) :
    (∫ x, (∫ y, Γ (G.mul (G.inv y) x) * φ y) * ψ x) =
      ∫ y, φ y * ∫ x, Γ (G.mul (G.inv y) x) * ψ x := by
  have hs := integral_integral_swap (f := fun y x => φ y * Γ (G.mul (G.inv y) x) * ψ x)
    (integrable_potential_pairing G hΓ hφ hcφ hψ hcψ)
  simp_rw [mul_assoc] at hs
  simp_rw [integral_const_mul] at hs
  simp_rw [← mul_assoc] at hs
  simp_rw [integral_mul_const] at hs
  simpa only [mul_comm, mul_left_comm, mul_assoc] using hs.symm

end RothschildStein.H1
