-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import Hormander.A.SobolevScale
public import Mathlib.Analysis.Fourier.FourierTransform
public import Mathlib.MeasureTheory.Function.LocallyIntegrable
public import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm
public import Mathlib.Analysis.SpecialFunctions.JapaneseBracket

@[expose] public section

noncomputable section

open MeasureTheory SchwartzMap
open scoped FourierTransform RealInnerProductSpace

namespace Hormander.A

/-- The Fourier integral of integrable data represents the
distributional Fourier transform of its regular distribution. -/
theorem integrable_fourier_identification {N : ℕ} {v : Carrier N → ℂ}
    (hv : Integrable v) (φ : 𝓢(Carrier N, ℂ)) :
    ∫ ξ, (Real.Lp.fourierTransform (hv.toL1 v) ξ) * φ ξ =
      (MeasureTheory.Lp.toTemperedDistribution (hv.toL1 v))
        (SchwartzMap.fourierTransformCLM ℂ φ) := by
  have hFubini :
      ∫ ξ, (Real.Lp.fourierTransform (hv.toL1 v) ξ) * φ ξ =
        ∫ x, v x *
          VectorFourier.fourierIntegral 𝐞 volume (innerₗ (Carrier N))
            (φ : Carrier N → ℂ) x := by
    calc
      _ = ∫ ξ,
          (VectorFourier.fourierIntegral 𝐞 volume (innerₗ (Carrier N)) v ξ) • φ ξ := by
        apply integral_congr_ae
        filter_upwards with ξ
        calc
          _ = 𝓕 (hv.toL1 v : Carrier N → ℂ) ξ * φ ξ := by
            rfl
          _ = (VectorFourier.fourierIntegral 𝐞 volume
                (innerₗ (Carrier N)) v ξ) • φ ξ := by
            have hft := Real.fourier_congr_ae (hv.coeFn_toL1) ξ
            have hft' : 𝓕 (hv.toL1 v : Carrier N → ℂ) ξ =
                VectorFourier.fourierIntegral 𝐞 volume (innerₗ (Carrier N)) v ξ := by
              exact hft
            rw [hft']
            simp [smul_eq_mul]
      _ = ∫ x, v x •
          VectorFourier.fourierIntegral 𝐞 volume (innerₗ (Carrier N))
            (φ : Carrier N → ℂ) x := by
        simpa only [flip_innerₗ, smul_eq_mul] using
          (VectorFourier.integral_fourierIntegral_smul_eq_flip
            (μ := volume) (ν := volume) (L := innerₗ (Carrier N))
            Real.continuous_fourierChar continuous_inner hv φ.integrable)
      _ = ∫ x, v x *
          VectorFourier.fourierIntegral 𝐞 volume (innerₗ (Carrier N))
            (φ : Carrier N → ℂ) x := by
        simp [smul_eq_mul]
  have hφ : ⇑(SchwartzMap.fourierTransformCLM ℂ φ) =
      VectorFourier.fourierIntegral 𝐞 volume (innerₗ (Carrier N))
        (φ : Carrier N → ℂ) := by
    calc
      _ = 𝓕 (φ : Carrier N → ℂ) := by
        simpa using SchwartzMap.fourier_coe φ
      _ = _ := rfl
  calc
    ∫ ξ, (Real.Lp.fourierTransform (hv.toL1 v) ξ) * φ ξ =
        ∫ x, v x *
          VectorFourier.fourierIntegral 𝐞 volume (innerₗ (Carrier N))
            (φ : Carrier N → ℂ) x := hFubini
    _ = ∫ x, (SchwartzMap.fourierTransformCLM ℂ φ) x •
          (hv.toL1 v : Carrier N → ℂ) x := by
      apply integral_congr_ae
      filter_upwards [hv.coeFn_toL1] with x hx
      rw [hφ, ← hx]
      ring
    _ = (MeasureTheory.Lp.toTemperedDistribution (hv.toL1 v))
          (SchwartzMap.fourierTransformCLM ℂ φ) := by
      rw [MeasureTheory.Lp.toTemperedDistribution_apply]

/-- The Japanese-bracket weight of order `-m` is square-integrable
whenever `2*m` exceeds the dimension. -/
theorem negative_bessel_weight_memLp {N : ℕ} {m : ℝ} (hm : (N : ℝ) < 2 * m) :
    MemLp (fun ξ : Carrier N ↦ (1 + ‖ξ‖ ^ 2) ^ (-m / 2)) 2 volume := by
  have hradial : Integrable (fun ξ : Carrier N ↦
      ((1 : ℝ) + ‖ξ‖ ^ 2) ^ (-(2 * m) / 2)) volume := by
    exact integrable_rpow_neg_one_add_norm_sq (E := Carrier N) (r := 2 * m) (by
      simpa [Carrier] using hm)
  have hbase : Continuous (fun ξ : Carrier N ↦ (1 : ℝ) + ‖ξ‖ ^ 2) := by fun_prop
  have hweight : Continuous (fun ξ : Carrier N ↦ (1 + ‖ξ‖ ^ 2) ^ (-m / 2)) :=
    hbase.rpow_const (fun ξ ↦ Or.inl (by positivity : (1 : ℝ) + ‖ξ‖ ^ 2 ≠ 0))
  rw [memLp_two_iff_integrable_sq_norm hweight.aestronglyMeasurable]
  convert hradial using 1
  ext ξ
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity :
    0 ≤ (1 + ‖ξ‖ ^ 2) ^ (-m / 2))]
  rw [← Real.rpow_natCast ((1 + ‖ξ‖ ^ 2) ^ (-m / 2)) 2,
    ← Real.rpow_mul (by positivity : 0 ≤ (1 + ‖ξ‖ ^ 2))]
  congr 1
  ring

/-- An integrable function defines a tempered distribution in
negative Sobolev order whenever the Japanese-bracket weight is square-integrable. -/
theorem memSobolev_neg_of_integrable {N : ℕ} {v : Carrier N → ℂ} (hv : Integrable v)
    {m : ℝ} (hm : (N : ℝ) < 2 * m) :
    TemperedDistribution.MemSobolev (-m) 2
      (MeasureTheory.Lp.toTemperedDistribution (hv.toL1 v)) := by
  let ft := Real.Lp.fourierTransform (hv.toL1 v)
  have hftTop : MemLp (fun ξ : Carrier N ↦ ft ξ) ⊤ volume := ft.memLp_top
  let ftLp : Lp ℂ ⊤ volume := hftTop.toLp ft
  have hfourier :
      𝓕 (MeasureTheory.Lp.toTemperedDistribution (hv.toL1 v) : 𝓢'(Carrier N, ℂ)) =
        (MeasureTheory.Lp.toTemperedDistribution ftLp : 𝓢'(Carrier N, ℂ)) := by
    ext φ
    rw [Hormander.A.tempered_fourier_apply]
    calc
      (MeasureTheory.Lp.toTemperedDistribution (hv.toL1 v))
          (𝓕 φ) =
          (MeasureTheory.Lp.toTemperedDistribution (hv.toL1 v))
            (SchwartzMap.fourierTransformCLM ℂ φ) := by
              congr 1
      _ =
          ∫ ξ, ft ξ * φ ξ := (integrable_fourier_identification hv φ).symm
      _ = (MeasureTheory.Lp.toTemperedDistribution ftLp) φ := by
        rw [MeasureTheory.Lp.toTemperedDistribution_apply]
        apply integral_congr_ae
        filter_upwards [hftTop.coeFn_toLp] with ξ hξ
        simp [ftLp, hξ, smul_eq_mul, mul_comm]
  have hweightR := negative_bessel_weight_memLp (N := N) (m := m) hm
  have hweightC : MemLp
      (fun ξ : Carrier N ↦ (Complex.ofReal ((1 + ‖ξ‖ ^ 2) ^ (-m / 2)))) 2 volume :=
    hweightR.ofReal
  let weightLp : Lp ℂ 2 volume := hweightC.toLp _
  have hmem : TemperedDistribution.MemSobolev (-m) 2
      (MeasureTheory.Lp.toTemperedDistribution (hv.toL1 v)) := by
    rw [TemperedDistribution.memSobolev_iff_exists_smulLeftCLM_fourier]
    refine ⟨(hweightC.toLp _) • ftLp, ?_⟩
    rw [MeasureTheory.Lp.toTemperedDistribution_smul_eq]
    · rw [← hfourier]
    · fun_prop
  exact hmem

end Hormander.A
