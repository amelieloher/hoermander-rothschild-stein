-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import Hormander.A.SmoothRepresentative.WeightedL1
public import Hormander.A.SmoothRepresentative.InverseIntegral

@[expose] public section

noncomputable section

open MeasureTheory SchwartzMap TemperedDistribution
open scoped FourierTransform

namespace Hormander.A

/-- If `v ∈ L¹` represents `𝓕 T`, then `f = 𝓕⁻ v`
represents `T`: `T φ = ∫ φ f` for every Schwartz `φ`, and `φ f` is integrable (`f` is bounded and
continuous). -/
theorem regular_distribution_identity {N : ℕ} {T : 𝓢'(Carrier N, ℂ)}
    (v : Lp ℂ 1 (volume : Measure (Carrier N))) (hv : 𝓕 T = (v : 𝓢'(Carrier N, ℂ)))
    (φ : 𝓢(Carrier N, ℂ)) :
    Integrable (fun x ↦ φ x * 𝓕⁻ (⇑v) x) ∧ T φ = ∫ x, φ x * 𝓕⁻ (⇑v) x := by
  have hvint : Integrable (⇑v) volume := memLp_one_iff_integrable.mp (Lp.memLp v)
  have hcont : Continuous (𝓕⁻ (⇑v) : Carrier N → ℂ) := by
    have := contDiff_fourierInv_of_integrable_moments (q := 0) (g := ⇑v) (by
      intro n hn
      have : n = 0 := Nat.le_zero.mp (by exact_mod_cast hn)
      subst this
      simpa using hvint.norm)
    exact this.continuous
  constructor
  · have hφ : Integrable (φ : Carrier N → ℂ) := φ.integrable
    have := Integrable.bdd_mul (c := ∫ ξ, ‖v ξ‖) hφ hcont.aestronglyMeasurable
      (Filter.Eventually.of_forall fun x => norm_fourierInv_le_integral_norm _ x)
    simpa [mul_comm] using this
  · have h1 : T φ = ∫ ξ, 𝓕⁻ φ ξ • v ξ := by
      calc T φ = (𝓕⁻ (𝓕 T)) φ := by rw [(tempered_fourier_inversion T).1]
        _ = (𝓕 T) (𝓕⁻ φ) := rfl
        _ = _ := by
          rw [hv]
          exact Lp.toTemperedDistribution_apply (μ := (volume : Measure (Carrier N))) v (𝓕⁻ φ)
    rw [h1, ← integral_smul_fourierInv_eq hvint φ]
    simp [smul_eq_mul]

/-- A tempered distribution lying in every `H^s` is given by a smooth function `f`:
`T φ = ∫ φ f` and `φ f` is integrable for every Schwartz `φ`. (Common Fourier representative:
`lp_eq_of_toTemperedDistribution_eq`; moments: `integrable_norm_pow_mul_fourier`; smoothness:
`contDiff_fourierInv_of_integrable_moments`.) -/
theorem exists_contDiff_of_forall_memSobolev {N : ℕ}
    {T : 𝓢'(EuclideanSpace ℝ (Fin N), ℂ)}
    (hT : ∀ s : ℝ, TemperedDistribution.MemSobolev s 2 T) :
    ∃ f : EuclideanSpace ℝ (Fin N) → ℂ,
      ContDiff ℝ (⊤ : ℕ∞) f ∧
        ∀ φ : 𝓢(EuclideanSpace ℝ (Fin N), ℂ),
          Integrable (fun x => φ x * f x) ∧ T φ = ∫ x, φ x * f x := by
  have hs : (N : ℝ) < 2 * ((N : ℝ) / 2 + 1) := by linarith
  obtain ⟨u, v, hv, -⟩ := exists_fourier_weight_mul hs (hT ((N : ℝ) / 2 + 1))
  refine ⟨𝓕⁻ (⇑v), ?_, fun φ => regular_distribution_identity v hv φ⟩
  refine contDiff_fourierInv_of_integrable_moments (fun n _ => ?_)
  exact integrable_norm_pow_mul_fourier (s := (n : ℝ) + N / 2 + 1) (n := n) (by linarith)
    (hT _) v hv

end Hormander.A
