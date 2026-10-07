-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import Hormander.A.Scale.Weighted

@[expose] public section

noncomputable section

open MeasureTheory SchwartzMap TemperedDistribution
open scoped FourierTransform BesselPotentialSpace ComplexConjugate

namespace Hormander.A

/-- Auxiliary: conjugation preserves the `L²` norm. -/
theorem norm_star_lp2 {N : ℕ} (f : Lp ℂ 2 (volume : Measure (Carrier N))) : ‖star f‖ = ‖f‖ := by
  simp only [Lp.norm_def]
  exact congrArg ENNReal.toReal ((eLpNorm_congr_ae (Lp.coeFn_star f)).trans eLpNorm_star)

/-- Auxiliary: the bilinear integral pairing is the `L²` inner product with the conjugated first
factor. -/
theorem integral_mul_eq_inner_star {N : ℕ} (f g : Lp ℂ 2 (volume : Measure (Carrier N))) :
    ∫ x, f x * g x = inner ℂ (star f) g := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [Lp.coeFn_star f] with x hx
  simp [hx, mul_comm]

/-- Auxiliary: bilinear Cauchy–Schwarz on `L²`. -/
theorem norm_integral_mul_le {N : ℕ} (f g : Lp ℂ 2 (volume : Measure (Carrier N))) :
    ‖∫ x, f x * g x‖ ≤ ‖f‖ * ‖g‖ := by
  rw [integral_mul_eq_inner_star, ← norm_star_lp2 f]
  exact norm_inner_le_norm _ _

/-- The pairing formula for `u ∈ H^{-s}` and Schwartz `φ`,
`⟨u, φ⟩ = ∫ (𝓕 ũ)(ξ) (J_s φ)(ξ) dξ`, where `ũ = u.toLp`. -/
theorem pairing_eq_integral {N : ℕ} (s : ℝ) (u : SobolevSpace N (-s)) (φ : 𝓢(Carrier N, ℂ)) :
    u.toDistr φ = ∫ ξ, Jschw s φ ξ * (𝓕 u.toLp : Lp ℂ 2 (volume : Measure (Carrier N))) ξ := by
  have hinv : u.toDistr = 𝓕⁻ (𝓕 u.toDistr) := (tempered_fourier_inversion u.toDistr).1.symm
  have hprod : TemperedDistribution.smulLeftCLM ℂ (besselSymbol (N := N) s)
      (TemperedDistribution.smulLeftCLM ℂ (besselSymbol (N := N) (-s)) (𝓕 u.toDistr)) =
      𝓕 u.toDistr := by
    rw [TemperedDistribution.smulLeftCLM_smulLeftCLM_apply
      (besselSymbol_hasTemperateGrowth _) (besselSymbol_hasTemperateGrowth _)]
    have : (besselSymbol (N := N) (-s) * besselSymbol (N := N) s) = fun _ => (1 : ℂ) := by
      ext ξ
      have := besselSymbol_neg_mul (N := N) s ξ
      simpa [besselSymbol] using this
    rw [this, TemperedDistribution.smulLeftCLM_const, one_smul]
  have hw := fourier_toLp_eq_weighted_fourier u
  calc u.toDistr φ = (𝓕 u.toDistr) (𝓕⁻ φ) := by
        conv_lhs => rw [hinv]
        rfl
    _ = (TemperedDistribution.smulLeftCLM ℂ (besselSymbol (N := N) s)
          (TemperedDistribution.smulLeftCLM ℂ (besselSymbol (N := N) (-s)) (𝓕 u.toDistr)))
          (𝓕⁻ φ) := by rw [hprod]
    _ = (TemperedDistribution.smulLeftCLM ℂ (besselSymbol (N := N) (-s)) (𝓕 u.toDistr))
          (SchwartzMap.smulLeftCLM ℂ (besselSymbol s) (𝓕⁻ φ)) := by
        rw [TemperedDistribution.smulLeftCLM_apply_apply]
    _ = _ := by
        rw [← Jschw_eq_smulLeft]
        have : TemperedDistribution.smulLeftCLM ℂ (besselSymbol (N := N) (-s)) (𝓕 u.toDistr) =
            (MeasureTheory.Lp.toTemperedDistribution (𝓕 (u.toLp)) : 𝓢'(Carrier N, ℂ)) := hw.symm
        rw [this, Lp.toTemperedDistribution_apply]
        simp [smul_eq_mul]

/-- Sharp bilinear duality bound `|⟨u,φ⟩| ≤ ‖u‖_{H^{-s}} ‖φ‖_{H^s}`. -/
theorem abs_pairing_le {N : ℕ} (s : ℝ) (u : SobolevSpace N (-s)) (φ : 𝓢(Carrier N, ℂ)) :
    ‖u.toDistr φ‖ ≤ ‖u‖ * ‖schwartzToSobolev s φ‖ := by
  rw [pairing_eq_integral]
  have hJ := (weighted_fourier_density s).2.1 φ
  have hcongr : ∫ ξ, Jschw s φ ξ * (𝓕 u.toLp : Lp ℂ 2 (volume : Measure (Carrier N))) ξ =
      ∫ ξ, ((Jschw s φ).toLp 2 (volume : Measure (Carrier N))) ξ *
        (𝓕 u.toLp : Lp ℂ 2 (volume : Measure (Carrier N))) ξ := by
    apply integral_congr_ae
    filter_upwards [(Jschw s φ).coeFn_toLp 2 (volume : Measure (Carrier N))] with x hx
    rw [hx]
  rw [hcongr]
  refine (norm_integral_mul_le _ _).trans ?_
  rw [hJ, Lp.norm_fourier_eq, BesselPotentialSpace.norm_toLp_eq, mul_comm]

/-- Complex conjugation on Schwartz functions. -/
def starSchwartz {N : ℕ} (φ : 𝓢(Carrier N, ℂ)) : 𝓢(Carrier N, ℂ) :=
  SchwartzMap.postcompCLM (𝕜 := ℝ) (Complex.conjCLE : ℂ →L[ℝ] ℂ) φ

theorem starSchwartz_apply {N : ℕ} (φ : 𝓢(Carrier N, ℂ)) (x : Carrier N) :
    starSchwartz φ x = conj (φ x) := by
  simp [starSchwartz]

theorem fourierInv_conj_aux {N : ℕ} (f : Carrier N → ℂ) (ξ : Carrier N) :
    𝓕⁻ (fun x => conj (f x)) ξ = conj (𝓕 f ξ) := by
  rw [Real.fourierInv_eq', Real.fourier_eq', ← integral_conj]
  congr 1
  funext v
  simp only [smul_eq_mul, map_mul]
  rw [← Complex.exp_conj]
  simp
  left
  have h2 : (starRingEnd ℂ) 2 = 2 := map_ofNat _ 2
  rw [h2]

/-- Auxiliary: the conjugation symmetry of the weighted Fourier map. -/
theorem norm_Jschw_star {N : ℕ} (s : ℝ) (φ : 𝓢(Carrier N, ℂ)) (ξ : Carrier N) :
    ‖Jschw s (starSchwartz φ) ξ‖ = ‖Jschw s φ (-ξ)‖ := by
  have hfun : (⇑(starSchwartz φ) : Carrier N → ℂ) = fun x => conj (φ x) := by
    funext x; exact starSchwartz_apply φ x
  have h1 : 𝓕 (starSchwartz φ) (-ξ) = conj (𝓕 φ ξ) := by
    rw [SchwartzMap.fourier_coe, ← Real.fourierInv_eq_fourier_neg, hfun, fourierInv_conj_aux]
    rfl
  rw [Jschw_apply_pointwise, Jschw_apply_pointwise, h1, neg_neg, norm_mul, norm_mul,
    Complex.norm_conj]
  simp [besselSymbol, norm_neg]

/-- Auxiliary: conjugation preserves the `H^s` norm of Schwartz functions. -/
theorem norm_schwartzToSobolev_star {N : ℕ} (s : ℝ) (φ : 𝓢(Carrier N, ℂ)) :
    ‖schwartzToSobolev s (starSchwartz φ)‖ = ‖schwartzToSobolev s φ‖ := by
  rw [← (weighted_fourier_density s).2.1, ← (weighted_fourier_density s).2.1]
  rw [SchwartzMap.norm_toLp, SchwartzMap.norm_toLp]
  congr 1
  have hpres : MeasurePreserving (fun x : Carrier N => -x) volume volume :=
    Measure.measurePreserving_neg _
  calc eLpNorm (Jschw s (starSchwartz φ)) 2 volume
      = eLpNorm (fun x => Jschw s φ (-x)) 2 volume :=
        eLpNorm_congr_norm_ae (Jschw s (starSchwartz φ)).continuous.aestronglyMeasurable
          ((Jschw s φ).continuous.comp continuous_neg).aestronglyMeasurable
          (Filter.Eventually.of_forall fun x => norm_Jschw_star s φ x)
    _ = eLpNorm (Jschw s φ) 2 volume := by
        have := eLpNorm_comp_measurePreserving (p := 2)
          (Jschw s φ).continuous.aestronglyMeasurable hpres
        exact this

end Hormander.A
