-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import Hormander.A.Mollifier.Convergence
public import Hormander.A.Mollifier.FourierSide
public import Hormander.A.Mollifier.SchwartzConvergenceEstimate

@[expose] public section

noncomputable section

open Filter SchwartzMap TemperedDistribution
open scoped FourierTransform Topology

namespace Hormander.A

/-- On the Fourier side, `g_δ φ - φ` with `g_δ = 𝓕 Jc (δ ·)` is
`O(δ)` in every Schwartz seminorm for `0 < δ ≤ 1`. -/
theorem fourierSide_seminorm_le {N : ℕ} (φ : 𝓢(Carrier N, ℂ)) {δ : ℝ} (hδ : 0 < δ)
    (hδ1 : δ ≤ 1) (k n : ℕ) :
    SchwartzMap.seminorm ℂ k n
        (SchwartzMap.smulLeftCLM ℂ (fun ξ : Carrier N => 𝓕 (Jc N) (δ • ξ)) φ - φ) ≤
      δ * dilationConst (𝓕 (Jc N)) φ k n :=
  seminorm_smulLeft_dilate_sub_le (𝓕 (Jc N)) φ fourier_Jc_zero hδ.le hδ1
    (hasTemperateGrowth_fourier_dilate δ hδ) k n

/-- The Fourier-side multipliers `g_δ φ` converge to `φ` in the
Schwartz topology as `δ ↓ 0`. -/
theorem fourierSide_tendsto {N : ℕ} (φ : 𝓢(Carrier N, ℂ)) :
    Tendsto (fun δ : ℝ => if 0 < δ then
        SchwartzMap.smulLeftCLM ℂ (fun ξ : Carrier N => 𝓕 (Jc N) (δ • ξ)) φ else φ)
      (𝓝[>] (0 : ℝ)) (𝓝 φ) := by
  rw [(schwartz_withSeminorms ℂ (Carrier N) ℂ).tendsto_nhds]
  rintro ⟨k, n⟩ ε hε
  set K := dilationConst (𝓕 (Jc N)) φ k n with hK
  have hK0 : 0 ≤ K := dilationConst_nonneg _ _ k n
  have hpos : 0 < min 1 (ε / (K + 1)) := lt_min one_pos (div_pos hε (by linarith))
  filter_upwards [Ioo_mem_nhdsGT hpos] with δ hδ
  obtain ⟨hδ0, hδ1⟩ := hδ
  simp only [hδ0, ↓reduceIte]
  have hδ1' : δ ≤ 1 := (hδ1.trans_le (min_le_left _ _)).le
  have hδ2 : δ < ε / (K + 1) := hδ1.trans_le (min_le_right _ _)
  have hb := fourierSide_seminorm_le φ hδ0 hδ1' k n
  calc _ ≤ δ * K := hb
    _ ≤ δ * (K + 1) := by gcongr; linarith
    _ < ε := by rwa [lt_div_iff₀ (by linarith)] at hδ2

/-- Convergence of the mollified Schwartz tests in the Schwartz
topology. -/
theorem SδSchwartz_tendsto {N : ℕ} (ψ : 𝓢(Carrier N, ℂ)) :
    Tendsto (fun δ : ℝ => if hδ : 0 < δ then SδSchwartz N δ hδ ψ else ψ)
      (𝓝[>] (0 : ℝ)) (𝓝 ψ) := by
  have h1 := fourierSide_tendsto (𝓕⁻ ψ)
  have h2 := ((SchwartzMap.fourierTransformCLM ℂ :
    𝓢(Carrier N, ℂ) →L[ℂ] 𝓢(Carrier N, ℂ)).continuous.tendsto (𝓕⁻ ψ)).comp h1
  rw [SchwartzMap.fourierTransformCLM_apply, FourierTransform.fourier_fourierInv_eq] at h2
  refine h2.congr (fun δ => ?_)
  by_cases hδ : 0 < δ
  · simp only [Function.comp_apply, hδ, ↓reduceIte, ↓reduceDIte,
      SchwartzMap.fourierTransformCLM_apply]
    exact (SδSchwartz_eq_fourier_smulLeft δ hδ ψ).symm
  · simp only [Function.comp_apply, hδ, ↓reduceIte, ↓reduceDIte,
      SchwartzMap.fourierTransformCLM_apply]
    exact FourierTransform.fourier_fourierInv_eq ψ

/-- Mollified tempered distributions converge to the distribution on every
Schwartz test function. -/
theorem Sδ_pairing_tendsto {N : ℕ} (T : 𝓢'(Carrier N, ℂ)) (ψ : 𝓢(Carrier N, ℂ)) :
    Tendsto (fun δ : ℝ => if hδ : 0 < δ then Sδ N δ hδ T ψ else T ψ)
      (𝓝[>] (0 : ℝ)) (𝓝 (T ψ)) :=
  Sδ_pairing_tendsto_of_Schwartz_tendsto T ψ (SδSchwartz_tendsto ψ)

end Hormander.A
