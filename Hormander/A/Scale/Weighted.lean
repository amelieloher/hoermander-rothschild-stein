-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import Hormander.A.SobolevScale
public import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier

@[expose] public section

noncomputable section

open MeasureTheory SchwartzMap TemperedDistribution
open scoped FourierTransform BesselPotentialSpace

namespace Hormander.A

/-- Auxiliary: the order-zero multiplier is the identity on Schwartz functions. -/
theorem Lambda_zero {N : ℕ} (φ : 𝓢(Carrier N, ℂ)) : Lambda (N := N) 0 φ = φ := by
  have h : 𝓕 (Lambda (N := N) 0 φ) = 𝓕 φ := by
    rw [fourier_Lambda]
    ext ξ
    rw [SchwartzMap.smulLeftCLM_apply_apply (besselSymbol_hasTemperateGrowth 0)]
    simp [besselSymbol]
  exact fourier_schwartz_bijective.1 (by simpa [SchwartzMap.fourierTransformCLM_apply] using h)

/-- Auxiliary: `Λ^s` is a bijection of Schwartz space. -/
theorem Lambda_bijective {N : ℕ} (s : ℝ) :
    Function.Bijective (Lambda (N := N) s) := by
  constructor
  · intro φ ψ h
    have := congrArg (Lambda (N := N) (-s)) h
    have e : ∀ χ : 𝓢(Carrier N, ℂ), Lambda (-s) (Lambda s χ) = χ := fun χ => by
      have := congrArg (fun A : 𝓢(Carrier N, ℂ) →L[ℂ] 𝓢(Carrier N, ℂ) => A χ)
        (Lambda_comp (N := N) (-s) s)
      simpa [Lambda_zero] using this
    simpa [e] using this
  · intro ψ
    refine ⟨Lambda (-s) ψ, ?_⟩
    have := congrArg (fun A : 𝓢(Carrier N, ℂ) →L[ℂ] 𝓢(Carrier N, ℂ) => A ψ)
      (Lambda_comp (N := N) s (-s))
    simpa [Lambda_zero] using this

/-- The weighted Fourier map `J_s φ (ξ) = ⟨ξ⟩^s φ̂(-ξ)`, realized
as the inverse Fourier transform of `Λ^s φ`. -/
def Jschw {N : ℕ} (s : ℝ) : 𝓢(Carrier N, ℂ) →L[ℂ] 𝓢(Carrier N, ℂ) :=
  (FourierTransform.fourierInvCLM ℂ 𝓢(Carrier N, ℂ)) ∘L Lambda s


theorem Jschw_apply {N : ℕ} (s : ℝ) (φ : 𝓢(Carrier N, ℂ)) :
    Jschw s φ = 𝓕⁻ (Lambda s φ) := rfl

/-- `J_s φ = ⟨ξ⟩^s 𝓕⁻ φ` pointwise (`φ̂(-ξ) = 𝓕⁻ φ ξ`). -/
theorem Jschw_eq_smulLeft {N : ℕ} (s : ℝ) (φ : 𝓢(Carrier N, ℂ)) :
    Jschw s φ = SchwartzMap.smulLeftCLM ℂ (besselSymbol s) (𝓕⁻ φ) := by
  ext ξ
  rw [Jschw_apply, SchwartzMap.smulLeftCLM_apply_apply (besselSymbol_hasTemperateGrowth s)]
  rw [SchwartzMap.fourierInv_coe, SchwartzMap.fourierInv_coe, Real.fourierInv_eq_fourier_neg,
    Real.fourierInv_eq_fourier_neg]
  have h := congrArg (fun ψ : 𝓢(Carrier N, ℂ) => ψ (-ξ)) (fourier_Lambda s φ)
  simp only [SchwartzMap.fourier_coe] at h
  rw [h, SchwartzMap.smulLeftCLM_apply_apply (besselSymbol_hasTemperateGrowth s),
    SchwartzMap.fourier_coe]
  simp [besselSymbol, norm_neg]


/-- `J_s` is a bijection of Schwartz space. -/
theorem Jschw_bijective {N : ℕ} (s : ℝ) : Function.Bijective (Jschw (N := N) s) := by
  have hinv : Function.Bijective
      (FourierTransform.fourierInvCLM ℂ 𝓢(Carrier N, ℂ) : 𝓢(Carrier N, ℂ) → 𝓢(Carrier N, ℂ)) := by
    constructor
    · intro φ ψ h
      simpa using congrArg (fun f : 𝓢(Carrier N, ℂ) => 𝓕 f) h
    · intro ψ
      exact ⟨𝓕 ψ, by simp⟩
  exact hinv.comp (Lambda_bijective s)

/-- `J_s` is an isometry from the `H^s` Schwartz norm to `L²`. -/
theorem norm_toLp_Jschw {N : ℕ} (s : ℝ) (φ : 𝓢(Carrier N, ℂ)) :
    ‖(Jschw s φ).toLp 2‖ = schwartzSobolevNorm s φ := by
  rw [Jschw_apply, ← SchwartzMap.toLp_fourierInv_eq, schwartzSobolevNorm]
  exact (Lp.fourierTransformₗᵢ (Carrier N) ℂ).symm.norm_map _


/-- Pointwise formula `J_s φ (ξ) = ⟨ξ⟩^s φ̂(-ξ)`. -/
theorem Jschw_apply_pointwise {N : ℕ} (s : ℝ) (φ : 𝓢(Carrier N, ℂ)) (ξ : Carrier N) :
    Jschw s φ ξ = besselSymbol s ξ * 𝓕 φ (-ξ) := by
  rw [Jschw_eq_smulLeft, SchwartzMap.smulLeftCLM_apply_apply (besselSymbol_hasTemperateGrowth s),
    SchwartzMap.fourierInv_coe, Real.fourierInv_eq_fourier_neg]
  rfl

/-- Auxiliary: the bundled `L²` representative of the Schwartz element of `H^s` is `Λ^s φ`. -/
theorem schwartzToSobolev_toLp {N : ℕ} (s : ℝ) (φ : 𝓢(Carrier N, ℂ)) :
    (schwartzToSobolev s φ).toLp = (Lambda s φ).toLp 2 := by
  have huDist : (schwartzToSobolev s φ).toDistr = (φ : 𝓢'(Carrier N, ℂ)) :=
    TemperedDistribution.MemSobolev.toBesselPotentialSpace_toDistr (schwartz_memSobolev s φ)
  have hdist :
      (MeasureTheory.Lp.toTemperedDistribution ((Lambda s φ).toLp 2) :
        𝓢'(Carrier N, ℂ)) =
        MeasureTheory.Lp.toTemperedDistribution (schwartzToSobolev s φ).toLp := by
    rw [← (schwartzToSobolev s φ).bessel_toDistr_eq_toLp, huDist,
      ← Lambda_toTemperedDistribution]
    simp
  exact ((LinearMap.ker_eq_bot.mp
      (MeasureTheory.Lp.ker_toTemperedDistributionCLM_eq_bot (F := ℂ)
        (μ := volume) (p := 2))) hdist).symm

/-- Auxiliary: Schwartz functions are dense in `L²`, in the form `DenseRange (toLp ∘ T)` for a
bijection `T` of Schwartz space. -/
theorem denseRange_toLp_comp_of_bijective {N : ℕ}
    {T : 𝓢(Carrier N, ℂ) → 𝓢(Carrier N, ℂ)} (hT : Function.Bijective T) :
    DenseRange (fun φ : 𝓢(Carrier N, ℂ) ↦ (T φ).toLp 2 (volume : Measure (Carrier N))) := by
  have h := SchwartzMap.denseRange_toLpCLM (E := Carrier N) (F := ℂ) (p := 2) (μ := volume)
    ENNReal.ofNat_ne_top
  have hr : Set.range (fun φ : 𝓢(Carrier N, ℂ) ↦ (T φ).toLp 2 (volume : Measure (Carrier N))) =
      Set.range (SchwartzMap.toLpCLM ℝ ℂ 2 (volume : Measure (Carrier N))) :=
    hT.2.range_comp
      (fun ψ : 𝓢(Carrier N, ℂ) ↦ ψ.toLp 2 (volume : Measure (Carrier N)))
  unfold DenseRange
  rw [hr]
  exact h

/-- The Schwartz images `J_s φ` are dense in `L²`. -/
theorem denseRange_Jschw_toLp {N : ℕ} (s : ℝ) :
    DenseRange (fun φ : 𝓢(Carrier N, ℂ) ↦ (Jschw s φ).toLp 2 (volume : Measure (Carrier N))) :=
  denseRange_toLp_comp_of_bijective (Jschw_bijective s)

/-- Schwartz functions are dense in `H^s`. -/
theorem denseRange_schwartzToSobolev {N : ℕ} (s : ℝ) :
    DenseRange (schwartzToSobolev (N := N) s) := by
  have h1 := denseRange_toLp_comp_of_bijective (Lambda_bijective (N := N) s)
  have h2 : DenseRange
      ((BesselPotentialSpace.toLpₗᵢ (Carrier N) ℂ s 2).symm :
        Lp ℂ 2 (volume : Measure (Carrier N)) → SobolevSpace N s) :=
    (BesselPotentialSpace.toLpₗᵢ (Carrier N) ℂ s 2).symm.toHomeomorph.surjective.denseRange
  have := h2.comp h1 (BesselPotentialSpace.toLpₗᵢ (Carrier N) ℂ s 2).symm.continuous
  convert this using 1
  funext φ
  apply BesselPotentialSpace.injective_toLp (Carrier N) ℂ s 2
  rw [schwartzToSobolev_toLp]
  have := (BesselPotentialSpace.toLpₗᵢ (Carrier N) ℂ s 2).apply_symm_apply
    ((Lambda s φ).toLp 2 (volume : Measure (Carrier N)))
  rw [BesselPotentialSpace.toLpₗᵢ_apply] at this
  exact this.symm

/-- `J_s` maps Schwartz space bijectively onto itself, isometrically
into `L²` for the `H^s` norm, with dense range in `L²`; hence Schwartz functions are dense in
`H^s`. -/
theorem weighted_fourier_density {N : ℕ} (s : ℝ) :
    Function.Bijective (Jschw (N := N) s) ∧
      (∀ φ : 𝓢(Carrier N, ℂ),
        ‖(Jschw s φ).toLp 2 (volume : Measure (Carrier N))‖ = ‖schwartzToSobolev s φ‖) ∧
      DenseRange (fun φ : 𝓢(Carrier N, ℂ) ↦ (Jschw s φ).toLp 2 (volume : Measure (Carrier N))) ∧
      DenseRange (schwartzToSobolev (N := N) s) :=
  ⟨Jschw_bijective s,
    fun φ ↦ (norm_toLp_Jschw s φ).trans (schwartzSobolevNorm_eq_schwartzToSobolev_norm s φ),
    denseRange_Jschw_toLp s, denseRange_schwartzToSobolev s⟩

end Hormander.A
