-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import Hormander.A.Mollifier.SchwartzConvergence
public import Hormander.A.Mollifier.Contraction
public import Mathlib.MeasureTheory.Function.LpSpace.ContinuousFunctions
public import Hormander.A.SmoothRepresentative.Main
public import Hormander.A.Scale.Riesz

@[expose] public section

noncomputable section

open Filter MeasureTheory SchwartzMap TemperedDistribution
open scoped BesselPotentialSpace FourierTransform Topology

namespace Hormander.A

/-- A pointwise limit (on Schwartz tests) of tempered distributions that
lie, eventually, in the ball of radius `C` of `H^s` again lies in that ball. This replaces the
Banach-Alaoglu step is replaced by Riesz duality: the uniform bound
`‖Tδ φ‖ ≤ C ‖φ‖_{H^{-s}}` passes to the limit and `riesz_converse` produces the representative. -/
theorem memSobolev_of_tendsto_of_bounded {N : ℕ} {s C : ℝ} {ι : Type*} {l : Filter ι} [l.NeBot]
    (Tδ : ι → 𝓢'(Carrier N, ℂ)) (T : 𝓢'(Carrier N, ℂ))
    (hbound : ∀ᶠ i in l, ∃ v : SobolevSpace N s, v.toDistr = Tδ i ∧ ‖v‖ ≤ C)
    (hlim : ∀ φ : 𝓢(Carrier N, ℂ), Tendsto (fun i => Tδ i φ) l (𝓝 (T φ))) :
    ∃ v : SobolevSpace N s, v.toDistr = T ∧ ‖v‖ ≤ C := by
  have hC : 0 ≤ C := by
    obtain ⟨i, v, -, hv⟩ := hbound.exists
    exact (norm_nonneg v).trans hv
  have hpair : ∀ φ : 𝓢(Carrier N, ℂ), ‖T φ‖ ≤ C * ‖schwartzToSobolev (-s) φ‖ := by
    intro φ
    refine le_of_tendsto (hlim φ).norm ?_
    filter_upwards [hbound] with i hi
    obtain ⟨v, hv, hvC⟩ := hi
    obtain ⟨v', hv', hv'v⟩ := sobolev_mono_norm (neg_neg s).le v
    rw [← hv, ← hv']
    exact (abs_pairing_le (-s) v' φ).trans
      (mul_le_mul_of_nonneg_right (hv'v.trans hvC) (norm_nonneg _))
  obtain ⟨w, hw, hwC⟩ := riesz_converse (-s) T hC hpair
  obtain ⟨w', hw', hw'w⟩ := sobolev_mono_norm (neg_neg s).ge w
  exact ⟨w', hw'.trans hw, hw'w.trans hwC⟩

/-- The converse for mollification, given that `Sδ T` converges to `T`
against each Schwartz test as `δ ↓ 0`. -/
theorem mollifier_weak_limit_converse_of_pairing {N : ℕ} {s : ℝ} (T : 𝓢'(Carrier N, ℂ))
    {C δ₀ : ℝ} (hδ₀ : 0 < δ₀)
    (hpair : ∀ ψ : 𝓢(Carrier N, ℂ),
      Tendsto (fun δ : ℝ => if hδ : 0 < δ then Sδ N δ hδ T ψ else T ψ) (𝓝[>] (0 : ℝ))
        (𝓝 (T ψ)))
    (h : ∀ (δ : ℝ) (hδ : 0 < δ), δ < δ₀ →
      ∃ v : SobolevSpace N s, v.toDistr = Sδ N δ hδ T ∧ ‖v‖ ≤ C) :
    (∃ v : SobolevSpace N s, v.toDistr = T ∧ ‖v‖ ≤ C) ∧
      ∃ h : Lp ℂ 2 (volume : Measure (Carrier N)), ‖h‖ ≤ C ∧
        𝓕 T = TemperedDistribution.smulLeftCLM ℂ (besselSymbol (N := N) (-s))
          (h : 𝓢'(Carrier N, ℂ)) := by
  let Tδ : ℝ → 𝓢'(Carrier N, ℂ) := fun δ => if hδ : 0 < δ then Sδ N δ hδ T else T
  have hv : ∃ v : SobolevSpace N s, v.toDistr = T ∧ ‖v‖ ≤ C := by
    refine memSobolev_of_tendsto_of_bounded (l := 𝓝[>] (0 : ℝ)) Tδ T ?_ ?_
    · filter_upwards [Ioo_mem_nhdsGT hδ₀] with δ hδ
      have hpos : 0 < δ := hδ.1
      simpa [Tδ, hpos] using h δ hpos hδ.2
    · intro φ
      refine (hpair φ).congr (fun δ => ?_)
      by_cases hδ : 0 < δ <;> simp [Tδ, hδ]
  refine ⟨hv, ?_⟩
  obtain ⟨v, hvT, hvC⟩ := hv
  refine ⟨𝓕 v.toLp, ?_, ?_⟩
  · rw [Lp.norm_fourier_eq, BesselPotentialSpace.norm_toLp_eq]
    exact hvC
  · have hw := fourier_toLp_eq_weighted_fourier v
    rw [hvT] at hw
    change _ = TemperedDistribution.smulLeftCLM ℂ (besselSymbol (N := N) s) (𝓕 T) at hw
    rw [hw, TemperedDistribution.smulLeftCLM_smulLeftCLM_apply
      (besselSymbol_hasTemperateGrowth _) (besselSymbol_hasTemperateGrowth _)]
    have : (besselSymbol (N := N) s * besselSymbol (N := N) (-s)) = fun _ => (1 : ℂ) := by
      ext ξ
      have := besselSymbol_neg_mul (N := N) s ξ
      have hst : star (besselSymbol (N := N) s ξ) = besselSymbol (N := N) s ξ := by
        simp [besselSymbol]
      rw [hst] at this
      simpa [mul_comm] using this
    rw [this, TemperedDistribution.smulLeftCLM_const, one_smul]

/-- Converse compactness for mollification: if `Sδ T ∈ H^s` with
`‖Sδ T‖ ≤ C` for all `0 < δ < δ₀`, then `T ∈ H^s` with `‖T‖ ≤ C`; moreover `𝓕 T = h ⟨ξ⟩^{-s}`
with `h ∈ L²` and `‖h‖₂ ≤ C`. -/
theorem mollifier_weak_limit_converse {N : ℕ} {s : ℝ} (T : 𝓢'(Carrier N, ℂ)) {C δ₀ : ℝ}
    (hδ₀ : 0 < δ₀)
    (h : ∀ (δ : ℝ) (hδ : 0 < δ), δ < δ₀ →
      ∃ v : SobolevSpace N s, v.toDistr = Sδ N δ hδ T ∧ ‖v‖ ≤ C) :
    (∃ v : SobolevSpace N s, v.toDistr = T ∧ ‖v‖ ≤ C) ∧
      ∃ h : Lp ℂ 2 (volume : Measure (Carrier N)), ‖h‖ ≤ C ∧
        𝓕 T = TemperedDistribution.smulLeftCLM ℂ (besselSymbol (N := N) (-s))
          (h : 𝓢'(Carrier N, ℂ)) :=
  mollifier_weak_limit_converse_of_pairing T hδ₀ (Sδ_pairing_tendsto T) h

end Hormander.A
