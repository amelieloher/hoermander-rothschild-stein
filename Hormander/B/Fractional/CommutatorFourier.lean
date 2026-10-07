-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import Hormander.B.Fractional.FourierMul
public import Hormander.B.Fractional.Peetre

@[expose] public section

noncomputable section

open MeasureTheory
open scoped FourierTransform

namespace Hormander.B

variable {N : ℕ}

/-- The Bessel symbol `⟨ξ⟩^σ` as a complex number. -/
def besselSym (σ : ℝ) (ξ : Carrier N) : ℂ := ((japBracket ξ ^ σ : ℝ) : ℂ)

theorem besselSymbol_eq_besselSym (σ : ℝ) (ξ : Carrier N) :
    Hormander.A.besselSymbol σ ξ = besselSym σ ξ := by
  have h := norm_besselSymbol σ ξ
  have hnn : 0 ≤ japBracket ξ ^ σ := Real.rpow_nonneg (japBracket_pos ξ).le σ
  simp only [Hormander.A.besselSymbol, Complex.norm_real, Real.norm_eq_abs] at h
  simp only [besselSym, Hormander.A.besselSymbol]
  congr 1
  rw [← h, abs_of_nonneg (by positivity)]

theorem fourier_lambdaOperator (σ : ℝ) (v : TestFunction N) (ξ : Carrier N) :
    𝓕 (lambdaOperator σ v) ξ = besselSym σ ξ * 𝓕 v ξ := by
  have : lambdaOperator σ v = Hormander.A.Lambda σ v := rfl
  rw [this, fourier_Lambda_apply, besselSymbol_eq_besselSym]

theorem multiplierOperator_apply (g u : TestFunction N) (x : Carrier N) :
    multiplierOperator g u x = g x * u x := by
  show (SchwartzMap.smulLeftCLM ℂ g u) x = g x * u x
  rw [SchwartzMap.smulLeftCLM_apply_apply g.hasTemperateGrowth]
  rfl

theorem integrable_conv (φ ψ : TestFunction N) (ξ : Carrier N) :
    Integrable (fun a : Carrier N => φ a * ψ (ξ - a)) := by
  have hb : ∃ C, ∀ a : Carrier N, ‖ψ (ξ - a)‖ ≤ C :=
    ⟨SchwartzMap.seminorm ℝ 0 0 ψ, fun a => by
      simpa using SchwartzMap.norm_le_seminorm ℝ ψ (ξ - a)⟩
  obtain ⟨C, hC⟩ := hb
  refine Integrable.mono' (φ.integrable.norm.mul_const C) ?_ ?_
  · exact (φ.continuous.mul (ψ.continuous.comp (continuous_const.sub continuous_id))).aestronglyMeasurable
  · refine Filter.Eventually.of_forall fun a => ?_
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left (hC a) (norm_nonneg _)

theorem fourier_sub_testFunction (f h : TestFunction N) : 𝓕 (f - h) = 𝓕 f - 𝓕 h := by
  simpa [SchwartzMap.fourierTransformCLM_apply] using
    (SchwartzMap.fourierTransformCLM ℂ : TestFunction N →L[ℂ] TestFunction N).map_sub f h

/-- (Fourier kernel) The Fourier transform of `[Λ^σ, M_g] u` is a convolution with the kernel difference. -/
theorem fourier_comm_mul (σ : ℝ) (g u : TestFunction N) (ξ : Carrier N) :
    𝓕 (operatorComm (lambdaOperator σ) (multiplierOperator g) u) ξ =
      ∫ a, 𝓕 g a * ((besselSym σ ξ - besselSym σ (ξ - a)) * 𝓕 u (ξ - a)) := by
  have e : operatorComm (lambdaOperator σ) (multiplierOperator g) u =
      lambdaOperator σ (multiplierOperator g u) -
        multiplierOperator g (lambdaOperator σ u) := rfl
  rw [e, fourier_sub_testFunction, sub_apply, fourier_lambdaOperator, fourier_mul_apply,
    fourier_mul_apply]
  have h1 := (integrable_conv (𝓕 g) (𝓕 u) ξ).const_mul (besselSym σ ξ)
  have h2 := integrable_conv (𝓕 g) (𝓕 (lambdaOperator σ u)) ξ
  have : (fun a : Carrier N => 𝓕 g a * ((besselSym σ ξ - besselSym σ (ξ - a)) * 𝓕 u (ξ - a))) =
      fun a => besselSym σ ξ * (𝓕 g a * 𝓕 u (ξ - a)) -
        𝓕 g a * 𝓕 (lambdaOperator σ u) (ξ - a) := by
    funext a
    rw [fourier_lambdaOperator]
    ring
  rw [this, integral_sub h1 h2, integral_const_mul]

/-- The mixed second difference of the Bessel symbol. -/
def symMixed (σ : ℝ) (ξ a b : Carrier N) : ℂ :=
  besselSym σ ξ - besselSym σ (ξ - a) - besselSym σ (ξ - b) + besselSym σ (ξ - a - b)

/-- The two-variable integrand attached to a coefficient function `c`. -/
def tripleIntegrand (g h u : TestFunction N) (ξ : Carrier N) (c : Carrier N → Carrier N → ℂ)
    (p : Carrier N × Carrier N) : ℂ :=
  𝓕 g p.1 * (𝓕 h p.2 * (c p.1 p.2 * 𝓕 u (ξ - p.1 - p.2)))

theorem continuous_besselSym (σ : ℝ) : Continuous fun ξ : Carrier N => besselSym σ ξ :=
  Complex.continuous_ofReal.comp (continuous_japBracket_rpow σ)

theorem norm_besselSym_shift (σ : ℝ) (ξ d : Carrier N) :
    ‖besselSym σ (ξ - d)‖ ≤ japBracket ξ ^ σ * peetreOmega d ^ |σ| := by
  have h := peetre_jap (ξ - d) ξ σ
  have hn : peetreOmega (-d) = peetreOmega d := by
    unfold peetreOmega japBracket bracketSq
    rw [norm_neg]
  rw [sub_sub_cancel_left, hn] at h
  simpa [besselSym, abs_of_nonneg (Real.rpow_nonneg (japBracket_pos _).le σ)] using h

theorem integrable_tripleIntegrand (g h u : TestFunction N) (ξ : Carrier N)
    (c : Carrier N → Carrier N → ℂ) (hc : Continuous fun p : Carrier N × Carrier N => c p.1 p.2)
    (M C : ℝ) (hC : 0 ≤ C) (hb : ∀ a b, ‖c a b‖ ≤ C * (peetreOmega a ^ M * peetreOmega b ^ M)) :
    Integrable (tripleIntegrand g h u ξ c) (volume.prod volume) := by
  obtain ⟨U, hU⟩ : ∃ U, ∀ x : Carrier N, ‖𝓕 u x‖ ≤ U :=
    ⟨SchwartzMap.seminorm ℝ 0 0 (𝓕 u), fun x => by
      simpa using SchwartzMap.norm_le_seminorm ℝ (𝓕 u) x⟩
  have hdom : Integrable (fun p : Carrier N × Carrier N =>
      (peetreOmega p.1 ^ M * ‖𝓕 g p.1‖) * (peetreOmega p.2 ^ M * ‖𝓕 h p.2‖) * (C * U)) (volume.prod volume) :=
    ((integrable_peetreOmega_mul (𝓕 g) M).mul_prod (integrable_peetreOmega_mul (𝓕 h) M)).mul_const _
  refine hdom.mono' ?_ ?_
  · unfold tripleIntegrand
    have hu : Continuous fun p : Carrier N × Carrier N => 𝓕 u (ξ - p.1 - p.2) :=
      (𝓕 u).continuous.comp ((continuous_const.sub continuous_fst).sub continuous_snd)
    exact ((𝓕 g).continuous.comp continuous_fst).mul (((𝓕 h).continuous.comp continuous_snd).mul
      (hc.mul hu)) |>.aestronglyMeasurable
  · refine Filter.Eventually.of_forall fun p => ?_
    unfold tripleIntegrand
    simp only [norm_mul]
    have hu := hU (ξ - p.1 - p.2)
    have hcb := hb p.1 p.2
    have h0 : 0 ≤ ‖𝓕 g p.1‖ := norm_nonneg _
    have h1 : 0 ≤ ‖𝓕 h p.2‖ := norm_nonneg _
    have h2 : 0 ≤ peetreOmega p.1 ^ M := Real.rpow_nonneg (peetreOmega_pos _).le M
    have h3 : 0 ≤ peetreOmega p.2 ^ M := Real.rpow_nonneg (peetreOmega_pos _).le M
    have h4 : 0 ≤ ‖c p.1 p.2‖ := norm_nonneg _
    have h5 : 0 ≤ C * (peetreOmega p.1 ^ M * peetreOmega p.2 ^ M) := by positivity
    calc ‖𝓕 g p.1‖ * (‖𝓕 h p.2‖ * (‖c p.1 p.2‖ * ‖𝓕 u (ξ - p.1 - p.2)‖))
        ≤ ‖𝓕 g p.1‖ * (‖𝓕 h p.2‖ * ((C * (peetreOmega p.1 ^ M * peetreOmega p.2 ^ M)) * U)) := by
          gcongr
      _ = _ := by ring

theorem norm_besselSym (σ : ℝ) (ξ : Carrier N) : ‖besselSym σ ξ‖ = japBracket ξ ^ σ := by
  simp [besselSym, abs_of_nonneg (Real.rpow_nonneg (japBracket_pos ξ).le σ)]

/-- Coefficient of the first nested term. -/
def nestedC1 (σ : ℝ) (ξ a _b : Carrier N) : ℂ := besselSym σ ξ - besselSym σ (ξ - a)

/-- Coefficient of the second nested term. -/
def nestedC2 (σ : ℝ) (ξ a b : Carrier N) : ℂ := besselSym σ (ξ - b) - besselSym σ (ξ - a - b)

/-- The constant bounding the nested coefficients. -/
def nestedConst (σ : ℝ) (ξ : Carrier N) : ℝ := 2 * japBracket ξ ^ σ * (1 + 2 ^ |σ|)

theorem nestedConst_nonneg (σ : ℝ) (ξ : Carrier N) : 0 ≤ nestedConst σ ξ := by
  unfold nestedConst
  have := Real.rpow_nonneg (japBracket_pos ξ).le σ
  positivity

theorem one_le_peetreOmega_rpow (x : Carrier N) {p : ℝ} (hp : 0 ≤ p) : 1 ≤ peetreOmega x ^ p :=
  Real.one_le_rpow (one_le_peetreOmega x) hp

theorem norm_nestedC1_le (σ : ℝ) (ξ a b : Carrier N) :
    ‖nestedC1 σ ξ a b‖ ≤ nestedConst σ ξ * (peetreOmega a ^ |σ| * peetreOmega b ^ |σ|) := by
  unfold nestedC1 nestedConst
  have hJ := Real.rpow_nonneg (japBracket_pos ξ).le σ
  have h1 := norm_besselSym_shift σ ξ a
  have ha := one_le_peetreOmega_rpow a (abs_nonneg σ)
  have hb := one_le_peetreOmega_rpow b (abs_nonneg σ)
  have h2 := norm_sub_le (besselSym σ ξ) (besselSym σ (ξ - a))
  rw [norm_besselSym] at h2
  have h4 : 0 ≤ (2 ^ |σ| : ℝ) := by positivity
  have hAB : peetreOmega a ^ |σ| ≤ peetreOmega a ^ |σ| * peetreOmega b ^ |σ| :=
    le_mul_of_one_le_right (by linarith) hb
  have hABn : 0 ≤ peetreOmega a ^ |σ| * peetreOmega b ^ |σ| := by nlinarith
  have step : ‖besselSym σ ξ - besselSym σ (ξ - a)‖ ≤
      2 * (japBracket ξ ^ σ * (peetreOmega a ^ |σ| * peetreOmega b ^ |σ|)) := by
    nlinarith [mul_le_mul_of_nonneg_left ha hJ, mul_le_mul_of_nonneg_left hAB hJ]
  calc _ ≤ _ := step
    _ ≤ _ := by
      have := mul_nonneg (mul_nonneg hJ hABn) h4
      nlinarith

theorem norm_nestedC2_le (σ : ℝ) (ξ a b : Carrier N) :
    ‖nestedC2 σ ξ a b‖ ≤ nestedConst σ ξ * (peetreOmega a ^ |σ| * peetreOmega b ^ |σ|) := by
  unfold nestedC2 nestedConst
  have hJ := Real.rpow_nonneg (japBracket_pos ξ).le σ
  have h1 := norm_besselSym_shift σ ξ b
  have h2 := norm_besselSym_shift σ ξ (a + b)
  rw [← sub_sub] at h2
  have hadd : peetreOmega (a + b) ^ |σ| ≤ 2 ^ |σ| * (peetreOmega a ^ |σ| * peetreOmega b ^ |σ|) := by
    calc peetreOmega (a + b) ^ |σ| ≤ (2 * (peetreOmega a * peetreOmega b)) ^ |σ| :=
          Real.rpow_le_rpow (peetreOmega_pos _).le (peetreOmega_add_le a b) (abs_nonneg σ)
      _ = _ := by
          rw [Real.mul_rpow (by norm_num) (mul_nonneg (peetreOmega_pos a).le (peetreOmega_pos b).le),
            Real.mul_rpow (peetreOmega_pos a).le (peetreOmega_pos b).le]
  have ha := one_le_peetreOmega_rpow a (abs_nonneg σ)
  have hb := one_le_peetreOmega_rpow b (abs_nonneg σ)
  have h4 : 0 ≤ (2 ^ |σ| : ℝ) := by positivity
  have hABn : 0 ≤ peetreOmega a ^ |σ| * peetreOmega b ^ |σ| := by nlinarith
  have hbB : peetreOmega b ^ |σ| ≤ peetreOmega a ^ |σ| * peetreOmega b ^ |σ| :=
    le_mul_of_one_le_left (by linarith) ha
  have h5 := norm_sub_le (besselSym σ (ξ - b)) (besselSym σ (ξ - a - b))
  have h6 := mul_le_mul_of_nonneg_left hadd hJ
  have h7 := mul_le_mul_of_nonneg_left hbB hJ
  nlinarith [mul_nonneg (mul_nonneg hJ hABn) h4]

theorem continuous_nestedC1 (σ : ℝ) (ξ : Carrier N) :
    Continuous fun p : Carrier N × Carrier N => nestedC1 σ ξ p.1 p.2 := by
  unfold nestedC1
  exact continuous_const.sub ((continuous_besselSym σ).comp (continuous_const.sub continuous_fst))

theorem continuous_nestedC2 (σ : ℝ) (ξ : Carrier N) :
    Continuous fun p : Carrier N × Carrier N => nestedC2 σ ξ p.1 p.2 := by
  unfold nestedC2
  exact ((continuous_besselSym σ).comp (continuous_const.sub continuous_snd)).sub
    ((continuous_besselSym σ).comp ((continuous_const.sub continuous_fst).sub continuous_snd))

theorem integrable_nestedC1 (σ : ℝ) (g h u : TestFunction N) (ξ : Carrier N) :
    Integrable (tripleIntegrand g h u ξ (nestedC1 σ ξ)) (volume.prod volume) :=
  integrable_tripleIntegrand g h u ξ _ (continuous_nestedC1 σ ξ) |σ| _ (nestedConst_nonneg σ ξ)
    (norm_nestedC1_le σ ξ)

theorem integrable_nestedC2 (σ : ℝ) (g h u : TestFunction N) (ξ : Carrier N) :
    Integrable (tripleIntegrand g h u ξ (nestedC2 σ ξ)) (volume.prod volume) :=
  integrable_tripleIntegrand g h u ξ _ (continuous_nestedC2 σ ξ) |σ| _ (nestedConst_nonneg σ ξ)
    (norm_nestedC2_le σ ξ)

/-- (Fourier kernel) The Fourier transform of `[[Λ^σ, M_g], M_h] u` as an iterated integral of the mixed second
difference of the Bessel symbol. -/
theorem fourier_comm_nested (σ : ℝ) (g h u : TestFunction N) (ξ : Carrier N) :
    𝓕 (operatorComm (operatorComm (lambdaOperator σ) (multiplierOperator g))
        (multiplierOperator h) u) ξ =
      ∫ a, ∫ b, tripleIntegrand g h u ξ (symMixed σ ξ) (a, b) := by
  have e : operatorComm (operatorComm (lambdaOperator σ) (multiplierOperator g))
        (multiplierOperator h) u =
      operatorComm (lambdaOperator σ) (multiplierOperator g) (multiplierOperator h u) -
        multiplierOperator h (operatorComm (lambdaOperator σ) (multiplierOperator g) u) := rfl
  have hI1 := integrable_nestedC1 σ g h u ξ
  have hI2 := integrable_nestedC2 σ g h u ξ
  have t1 : 𝓕 (operatorComm (lambdaOperator σ) (multiplierOperator g) (multiplierOperator h u)) ξ =
      ∫ z, tripleIntegrand g h u ξ (nestedC1 σ ξ) z ∂(volume.prod volume) := by
    rw [fourier_comm_mul, integral_prod _ hI1]
    refine integral_congr_ae (Filter.Eventually.of_forall fun a => ?_)
    simp only [tripleIntegrand, nestedC1]
    rw [fourier_mul_apply, ← integral_const_mul, ← integral_const_mul]
    congr 1
    funext b
    ring
  have t2 : 𝓕 (multiplierOperator h
        (operatorComm (lambdaOperator σ) (multiplierOperator g) u)) ξ =
      ∫ z, tripleIntegrand g h u ξ (nestedC2 σ ξ) z ∂(volume.prod volume) := by
    rw [fourier_mul_apply, integral_prod_symm _ hI2]
    refine integral_congr_ae (Filter.Eventually.of_forall fun b => ?_)
    simp only [tripleIntegrand, nestedC2]
    rw [fourier_comm_mul, ← integral_const_mul]
    congr 1
    funext a
    rw [sub_right_comm ξ b a]
    ring
  have hs : (fun z => tripleIntegrand g h u ξ (nestedC1 σ ξ) z -
      tripleIntegrand g h u ξ (nestedC2 σ ξ) z) =
      tripleIntegrand g h u ξ (symMixed σ ξ) := by
    funext z
    simp only [tripleIntegrand, nestedC1, nestedC2, symMixed]
    ring
  have hI : Integrable (tripleIntegrand g h u ξ (symMixed σ ξ)) (volume.prod volume) := by
    rw [← hs]; exact hI1.sub hI2
  rw [e, fourier_sub_testFunction, sub_apply, t1, t2, ← integral_sub hI1 hI2, hs]
  exact integral_prod _ hI

end Hormander.B
