-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import Hormander.A.Fourier
public import Mathlib.Analysis.Distribution.Sobolev
public import Mathlib.Analysis.FunctionalSpaces.BesselPotentialSpace

@[expose] public section

noncomputable section

open MeasureTheory SchwartzMap TemperedDistribution
open scoped BesselPotentialSpace BoundedContinuousFunction ComplexInnerProductSpace FourierTransform

namespace Hormander.A

/-- The project's Sobolev space is Mathlib's bundled Bessel-potential space at p = 2. -/
abbrev SobolevSpace (N : ℕ) (s : ℝ) :=
  BesselPotentialSpace (Carrier N) ℂ s 2

/-- The complex-valued Japanese-bracket symbol. -/
def besselSymbol {N : ℕ} (s : ℝ) : Carrier N → ℂ :=
  fun ξ ↦ Complex.ofReal ((1 + ‖ξ‖ ^ 2) ^ (s / 2))

/-- The Bessel symbol has temperate growth. -/
theorem besselSymbol_hasTemperateGrowth {N : ℕ} (s : ℝ) :
    (besselSymbol (N := N) s).HasTemperateGrowth := by
  exact Function.HasTemperateGrowth.comp Complex.hasTemperateGrowth_ofReal
    (Function.hasTemperateGrowth_one_add_norm_sq_rpow (Carrier N) (s / 2))

/-- Opposite orders have reciprocal symbols. -/
theorem besselSymbol_neg_mul {N : ℕ} (s : ℝ) (ξ : Carrier N) :
    besselSymbol (-s) ξ * star (besselSymbol s ξ) = 1 := by
  simp only [besselSymbol, Complex.star_def, Complex.conj_ofReal]
  rw [← Complex.ofReal_mul, ← Real.rpow_add (by positivity : 0 < 1 + ‖ξ‖ ^ 2)]
  have hexp : -s / 2 + s / 2 = 0 := by ring
  rw [hexp, Real.rpow_zero]
  norm_num

/-- The Japanese-bracket Fourier multiplier on Schwartz functions. -/
def Lambda {N : ℕ} (s : ℝ) : 𝓢(Carrier N, ℂ) →L[ℂ] 𝓢(Carrier N, ℂ) :=
  SchwartzMap.fourierMultiplierCLM ℂ (besselSymbol s)

/-- Fourier transformation turns Lambda into its symbol. -/
theorem fourier_Lambda {N : ℕ} (s : ℝ) (φ : 𝓢(Carrier N, ℂ)) :
    𝓕 (Lambda s φ) =
      SchwartzMap.smulLeftCLM ℂ (besselSymbol s) (𝓕 φ) := by
  simp [Lambda, SchwartzMap.fourierMultiplierCLM_apply]

/-- The Bessel multiplier powers compose by adding their orders. -/
theorem Lambda_comp {N : ℕ} (s t : ℝ) :
    Lambda (N := N) s ∘L Lambda (N := N) t = Lambda (N := N) (s + t) := by
  rw [Lambda, Lambda, Lambda,
    SchwartzMap.fourierMultiplierCLM_compL_fourierMultiplierCLM
      (besselSymbol_hasTemperateGrowth s) (besselSymbol_hasTemperateGrowth t)]
  congr 1
  ext ξ
  simp only [Pi.mul_apply, besselSymbol]
  rw [← Complex.ofReal_mul]
  rw [← Real.rpow_add (by positivity)]
  congr 1
  ring_nf

/-- The inhomogeneous Sobolev norm on Schwartz functions. -/
def schwartzSobolevNorm {N : ℕ} (s : ℝ) (φ : 𝓢(Carrier N, ℂ)) : ℝ :=
  ‖(Lambda s φ).toLp 2‖

/-- Applying Lambda s shifts the Fourier Sobolev order by s. -/
theorem Lambda_sobolevNorm {N : ℕ} (s t : ℝ) (φ : 𝓢(Carrier N, ℂ)) :
    schwartzSobolevNorm t (Lambda s φ) = schwartzSobolevNorm (s + t) φ := by
  have hcomp : Lambda t (Lambda s φ) = Lambda (t + s) φ := by
    simpa [ContinuousLinearMap.comp_apply] using
      congrArg (fun A : 𝓢(Carrier N, ℂ) →L[ℂ] 𝓢(Carrier N, ℂ) => A φ)
        (Lambda_comp (N := N) t s)
  simp [schwartzSobolevNorm, hcomp, add_comm]

/-- The positive and negative Bessel multipliers preserve the
bilinear L2 pairing. -/
theorem Lambda_pairing {N : ℕ} (s : ℝ) (φ ψ : 𝓢(Carrier N, ℂ)) :
    ∫ x, ⟪Lambda s φ x, Lambda (-s) ψ x⟫ = ∫ x, ⟪φ x, ψ x⟫ := by
  calc
    ∫ x, ⟪Lambda s φ x, Lambda (-s) ψ x⟫ =
        ∫ ξ, ⟪𝓕 (Lambda s φ) ξ, 𝓕 (Lambda (-s) ψ) ξ⟫ :=
      (Hormander.A.fourier_schwartz_plancherel (Lambda s φ) (Lambda (-s) ψ)).symm
    _ = ∫ ξ, ⟪𝓕 φ ξ, 𝓕 ψ ξ⟫ := by
      apply integral_congr_ae
      filter_upwards with ξ
      rw [fourier_Lambda s φ, fourier_Lambda (-s) ψ]
      rw [SchwartzMap.smulLeftCLM_apply_apply (besselSymbol_hasTemperateGrowth s)]
      rw [SchwartzMap.smulLeftCLM_apply_apply (besselSymbol_hasTemperateGrowth (-s))]
      rw [inner_smul_left, inner_smul_right]
      simp only [starRingEnd_apply]
      calc
        _ = (besselSymbol (-s) ξ * star (besselSymbol s ξ)) *
              ⟪(𝓕 φ) ξ, (𝓕 ψ) ξ⟫ := by ring_nf
        _ = _ := by rw [besselSymbol_neg_mul]; simp
    _ = ∫ x, ⟪φ x, ψ x⟫ :=
      Hormander.A.fourier_schwartz_plancherel φ ψ

/-- The Fourier representative of the Bessel potential has the
weighted distributional Fourier transform. -/
theorem fourier_toLp_eq_weighted_fourier {N : ℕ} {s : ℝ} (f : SobolevSpace N s) :
    (MeasureTheory.Lp.toTemperedDistribution (𝓕 (f.toLp)) : 𝓢'(Carrier N, ℂ)) =
      TemperedDistribution.smulLeftCLM ℂ
        (fun ξ : Carrier N ↦ ((1 + ‖ξ‖ ^ 2) ^ (s / 2) : ℝ))
        (𝓕 f.toDistr) := by
  calc
    (MeasureTheory.Lp.toTemperedDistribution (𝓕 (f.toLp)) : 𝓢'(Carrier N, ℂ)) =
        𝓕 (f.toLp : 𝓢'(Carrier N, ℂ)) := by
      exact (MeasureTheory.Lp.fourier_toTemperedDistribution_eq f.toLp).symm
    _ =
        𝓕 (TemperedDistribution.besselPotential (Carrier N) ℂ s f.toDistr) := by
      rw [f.bessel_toDistr_eq_toLp]
    _ = _ :=
      TemperedDistribution.fourier_besselPotential_eq_smulLeftCLM_fourier_apply s f.toDistr

/-- Every Schwartz function belongs to each Sobolev order. -/
theorem schwartz_memSobolev {N : ℕ} (s : ℝ) (φ : 𝓢(Carrier N, ℂ)) :
    TemperedDistribution.MemSobolev s 2 (φ : 𝓢'(Carrier N, ℂ)) :=
  SchwartzMap.memSobolev φ

/-- Every Schwartz function gives an element of the bundled Sobolev
space at every real order. -/
def schwartzToSobolev {N : ℕ} (s : ℝ) (φ : 𝓢(Carrier N, ℂ)) : SobolevSpace N s :=
  (schwartz_memSobolev s φ).toBesselPotentialSpace

/-- The Schwartz multiplier is the restriction of Mathlib's distributional Bessel potential. -/
theorem Lambda_toTemperedDistribution {N : ℕ} (s : ℝ) (φ : 𝓢(Carrier N, ℂ)) :
    (Lambda s φ : 𝓢'(Carrier N, ℂ)) =
      TemperedDistribution.besselPotential (Carrier N) ℂ s (φ : 𝓢'(Carrier N, ℂ)) := by
  symm
  change TemperedDistribution.fourierMultiplierCLM ℂ
      (fun ξ : Carrier N ↦ (((1 + ‖ξ‖ ^ 2) ^ (s / 2) : ℝ) : ℂ))
      (φ : 𝓢'(Carrier N, ℂ)) =
    (SchwartzMap.fourierMultiplierCLM ℂ
      (fun ξ : Carrier N ↦ (((1 + ‖ξ‖ ^ 2) ^ (s / 2) : ℝ) : ℂ)) φ :
        𝓢'(Carrier N, ℂ))
  exact TemperedDistribution.fourierMultiplierCLM_toTemperedDistributionCLM_eq
    (by fun_prop) φ

/-- The Schwartz Sobolev norm agrees with the norm of its bundled
Bessel-potential representative. -/
theorem schwartzSobolevNorm_eq_schwartzToSobolev_norm {N : ℕ} (s : ℝ)
    (φ : 𝓢(Carrier N, ℂ)) :
    schwartzSobolevNorm s φ = ‖schwartzToSobolev s φ‖ := by
  have huDist : (schwartzToSobolev s φ).toDistr = (φ : 𝓢'(Carrier N, ℂ)) :=
    TemperedDistribution.MemSobolev.toBesselPotentialSpace_toDistr (schwartz_memSobolev s φ)
  have hdist :
      (MeasureTheory.Lp.toTemperedDistribution ((Lambda s φ).toLp 2) :
        𝓢'(Carrier N, ℂ)) =
        MeasureTheory.Lp.toTemperedDistribution (schwartzToSobolev s φ).toLp := by
    rw [← (schwartzToSobolev s φ).bessel_toDistr_eq_toLp, huDist,
      ← Lambda_toTemperedDistribution]
    simp
  have hLp : (Lambda s φ).toLp 2 = (schwartzToSobolev s φ).toLp :=
    (LinearMap.ker_eq_bot.mp
      (MeasureTheory.Lp.ker_toTemperedDistributionCLM_eq_bot (F := ℂ)
        (μ := volume) (p := 2))) hdist
  rw [← BesselPotentialSpace.norm_toLp_eq, ← hLp]
  rfl

/-- Lowering the Sobolev order preserves the distribution and does not
increase the bundled norm. -/
theorem sobolev_mono_norm {N : ℕ} {s₁ s₂ : ℝ} (h : s₁ ≤ s₂)
    (u : SobolevSpace N s₂) :
    ∃ v : SobolevSpace N s₁, v.toDistr = u.toDistr ∧ ‖v‖ ≤ ‖u‖ := by
  have hexp : (s₁ - s₂) / 2 ≤ 0 := by linarith
  have hbound (ξ : Carrier N) : ‖besselSymbol (N := N) (s₁ - s₂) ξ‖ ≤ 1 := by
    simp only [besselSymbol, Complex.norm_real, Real.norm_eq_abs]
    rw [abs_of_nonneg (by positivity)]
    exact Real.rpow_le_one_of_one_le_of_nonpos
      (by nlinarith [sq_nonneg ‖ξ‖]) hexp
  let ratioB : Carrier N →ᵇ ℂ :=
    BoundedContinuousFunction.ofNormedAddCommGroup
      (besselSymbol (N := N) (s₁ - s₂))
      (besselSymbol_hasTemperateGrowth (N := N) (s₁ - s₂)).1.continuous 1 hbound
  let ratioLp : Lp ℂ ⊤ (volume : Measure (Carrier N)) := ratioB.memLp_top.toLp ratioB
  have hratioLp : ‖ratioLp‖ ≤ 1 := by
    dsimp [ratioLp]
    rw [Lp.norm_toLp]
    have hratioBound (ξ : Carrier N) : ‖ratioB ξ‖ ≤ 1 := by
      change ‖besselSymbol (N := N) (s₁ - s₂) ξ‖ ≤ 1
      exact hbound ξ
    have hess : eLpNorm ratioB ⊤ (volume : Measure (Carrier N)) ≤ 1 := by
      rw [eLpNorm_exponent_top (by fun_prop)]
      simpa using eLpNormEssSup_le_of_ae_bound
        (Filter.Eventually.of_forall hratioBound)
    exact ENNReal.toReal_mono (by simp) hess
  have hsymbol :
      besselSymbol (N := N) s₂ * besselSymbol (N := N) (s₁ - s₂) =
        besselSymbol (N := N) s₁ := by
    ext ξ
    simp only [Pi.mul_apply, besselSymbol]
    rw [← Complex.ofReal_mul, ← Real.rpow_add (by positivity)]
    congr 1
    ring_nf
  have hmem : TemperedDistribution.MemSobolev s₁ 2 u.toDistr :=
    (BesselPotentialSpace.memSobolev_toDistr u).mono h
  let v : SobolevSpace N s₁ := hmem.toBesselPotentialSpace
  have hproduct :
      (MeasureTheory.Lp.toTemperedDistribution (ratioLp • 𝓕 (u.toLp)) :
        𝓢'(Carrier N, ℂ)) =
        TemperedDistribution.smulLeftCLM ℂ (besselSymbol (N := N) (s₁ - s₂))
          (MeasureTheory.Lp.toTemperedDistribution (𝓕 (u.toLp))) := by
    dsimp [ratioLp]
    exact MeasureTheory.Lp.toTemperedDistribution_smul_eq
      (besselSymbol_hasTemperateGrowth (N := N) (s₁ - s₂)) ratioB.memLp_top (𝓕 (u.toLp))
  have hdist :
      (MeasureTheory.Lp.toTemperedDistribution (𝓕 (v.toLp)) : 𝓢'(Carrier N, ℂ)) =
        MeasureTheory.Lp.toTemperedDistribution (ratioLp • 𝓕 (u.toLp)) := by
    calc
      _ = TemperedDistribution.smulLeftCLM ℂ
            (fun ξ : Carrier N ↦ ((1 + ‖ξ‖ ^ 2) ^ (s₁ / 2) : ℝ))
            (𝓕 v.toDistr) := fourier_toLp_eq_weighted_fourier v
      _ = TemperedDistribution.smulLeftCLM ℂ
            (fun ξ : Carrier N ↦ ((1 + ‖ξ‖ ^ 2) ^ (s₁ / 2) : ℝ))
            (𝓕 u.toDistr) := by rw [hmem.toBesselPotentialSpace_toDistr]
      _ = TemperedDistribution.smulLeftCLM ℂ (besselSymbol (N := N) (s₁ - s₂))
            (MeasureTheory.Lp.toTemperedDistribution (𝓕 (u.toLp))) := by
        rw [fourier_toLp_eq_weighted_fourier u]
        rw [TemperedDistribution.smulLeftCLM_smulLeftCLM_apply
          (by fun_prop) (besselSymbol_hasTemperateGrowth (N := N) (s₁ - s₂))]
        change TemperedDistribution.smulLeftCLM ℂ (besselSymbol (N := N) s₁)
            (𝓕 u.toDistr) =
          TemperedDistribution.smulLeftCLM ℂ
            (besselSymbol (N := N) s₂ * besselSymbol (N := N) (s₁ - s₂))
            (𝓕 u.toDistr)
        rw [← hsymbol]
      _ = _ := hproduct.symm
  have hfourier : 𝓕 (v.toLp) = ratioLp • 𝓕 (u.toLp) :=
    (LinearMap.ker_eq_bot.mp
      (MeasureTheory.Lp.ker_toTemperedDistributionCLM_eq_bot (F := ℂ)
        (μ := volume) (p := 2))) hdist
  refine ⟨v, hmem.toBesselPotentialSpace_toDistr, ?_⟩
  calc
    ‖v‖ = ‖v.toLp‖ := (BesselPotentialSpace.norm_toLp_eq v).symm
    _ = ‖𝓕 (v.toLp)‖ := (MeasureTheory.Lp.norm_fourier_eq v.toLp).symm
    _ = ‖ratioLp • 𝓕 (u.toLp)‖ := congrArg norm hfourier
    _ ≤ ‖ratioLp‖ * ‖𝓕 (u.toLp)‖ := Lp.norm_smul_le ratioLp (𝓕 (u.toLp))
    _ ≤ 1 * ‖𝓕 (u.toLp)‖ := mul_le_mul_of_nonneg_right hratioLp (norm_nonneg _)
    _ = ‖u‖ := by simp [BesselPotentialSpace.norm_toLp_eq]

end Hormander.A
