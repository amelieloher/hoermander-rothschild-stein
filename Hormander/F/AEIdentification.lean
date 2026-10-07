-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.MeasureTheory.Measure.OpenPos
public import Mathlib.Analysis.Calculus.ContDiff.Basic
public import Mathlib.MeasureTheory.Function.LocallyIntegrable
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.Topology.Algebra.Support

@[expose] public section

noncomputable section

open Function MeasureTheory Set Topology

namespace Hormander.F

/-- If a smooth test is supported in an open set, its product
with any function vanishes outside that open set. -/
theorem compact_test_localization {E : Type*} [NormedAddCommGroup E]
    [MeasureSpace E]
    [NormedSpace ℝ E] {V : Set E} (_hV : IsOpen V) (h : E → ℝ)
    (φ : E → ℝ) (_hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (_hcompact : HasCompactSupport φ) (hsupport : tsupport φ ⊆ V) :
    ∫ x in V, φ x * h x = ∫ x, φ x * h x := by
  apply setIntegral_eq_integral_of_forall_compl_eq_zero
  intro x hxV
  have hxK : x ∉ tsupport φ := fun hx => hxV (hsupport hx)
  have hxS : x ∉ support φ := fun hx => hxK (subset_closure hx)
  have hφx : φ x = 0 := by
    simpa only [mem_support, not_not] using hxS
  simp [hφx]

/-- A locally integrable function on an open set vanishes almost
everywhere there if every supported smooth test has zero integral. -/
theorem ae_eq_zero_of_open_test_integrals {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [MeasureSpace E] [BorelSpace E]
    {V : Set E} (hV : IsOpen V) (h : E → ℝ)
    (hLoc : LocallyIntegrableOn h V volume)
    (hTest : ∀ φ : E → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
      tsupport φ ⊆ V → ∫ x in V, h x * φ x = 0) :
    ∀ᵐ x ∂volume, x ∈ V → h x = 0 := by
  have hmain := hV.ae_eq_zero_of_integral_contDiff_smul_eq_zero hLoc
    (fun φ hφ hcompact hsupport => by
      have hLocal := hTest φ hφ hcompact hsupport
      have hGlobal : ∫ x, φ x * h x = 0 := by
        rw [← compact_test_localization hV h φ hφ hcompact hsupport]
        simpa [mul_comm] using hLocal
      simpa only [smul_eq_mul] using hGlobal)
  simpa using hmain

/-- Equality of regular distributions on an open set implies
almost-everywhere equality of their locally integrable representatives. -/
theorem ae_eq_of_open_test_integrals {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [MeasureSpace E] [BorelSpace E]
    [IsLocallyFiniteMeasure (volume : Measure E)]
    {V : Set E} (hV : IsOpen V) (v f : E → ℝ)
    (hv : LocallyIntegrableOn v V volume)
    (hf : ContDiffOn ℝ (⊤ : ℕ∞) f V)
    (hTest : ∀ φ : E → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
      tsupport φ ⊆ V → ∫ x in V, v x * φ x = ∫ x in V, f x * φ x) :
    ∀ᵐ x ∂volume, x ∈ V → v x = f x := by
  have hfLoc : LocallyIntegrableOn f V volume :=
    hf.continuousOn.locallyIntegrableOn hV.measurableSet
  have hTestDiff : ∀ φ : E → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
      tsupport φ ⊆ V → ∫ x in V, (v x - f x) * φ x = 0 := by
    intro φ hφ hcompact hsupport
    have hVint : IntegrableOn (fun x => v x * φ x) V volume := by
      have hvK : IntegrableOn v (tsupport φ) volume :=
        (hv.mono_set hsupport).integrableOn_isCompact hcompact
      have hprodK : IntegrableOn (fun x => v x * φ x) (tsupport φ) volume :=
        hvK.mul_continuousOn hφ.continuous.continuousOn hcompact
      have hsup : support (fun x => v x * φ x) ⊆ tsupport φ := by
        exact (support_mul_subset_right _ _).trans (subset_tsupport φ)
      exact ((integrableOn_iff_integrable_of_support_subset hsup).mp hprodK).integrableOn
    have hFint : IntegrableOn (fun x => f x * φ x) V volume := by
      have hfK : IntegrableOn f (tsupport φ) volume :=
        (hfLoc.mono_set hsupport).integrableOn_isCompact hcompact
      have hprodK : IntegrableOn (fun x => f x * φ x) (tsupport φ) volume :=
        hfK.mul_continuousOn hφ.continuous.continuousOn hcompact
      have hsup : support (fun x => f x * φ x) ⊆ tsupport φ := by
        exact (support_mul_subset_right _ _).trans (subset_tsupport φ)
      exact ((integrableOn_iff_integrable_of_support_subset hsup).mp hprodK).integrableOn
    rw [show (fun x => (v x - f x) * φ x) =
        (fun x => v x * φ x) - fun x => f x * φ x by
          funext x
          simp [sub_mul, Pi.sub_apply]]
    have hVrestricted : Integrable (fun x => v x * φ x) (volume.restrict V) := hVint
    have hFrestricted : Integrable (fun x => f x * φ x) (volume.restrict V) := hFint
    change ∫ x in V, (v x * φ x - f x * φ x) = 0
    rw [MeasureTheory.integral_sub (μ := volume.restrict V) hVrestricted hFrestricted]
    exact sub_eq_zero.mpr (hTest φ hφ hcompact hsupport)
  have hDiffLoc : LocallyIntegrableOn (fun x => v x - f x) V volume :=
    hv.sub hfLoc
  have hzero := ae_eq_zero_of_open_test_integrals hV (fun x => v x - f x)
    hDiffLoc hTestDiff
  filter_upwards [hzero] with x hx
  exact fun hxV => sub_eq_zero.mp (hx hxV)

/-- Taking the real component of a complex smooth function preserves smoothness
on the same open set. -/
theorem realPart_contDiffOn {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {V : Set E} (F : E → ℂ)
    (hF : ContDiffOn ℝ (⊤ : ℕ∞) F V) :
    ContDiffOn ℝ (⊤ : ℕ∞) (fun x => (F x).re) V := by
  have h := Complex.reCLM.contDiff.comp_contDiffOn hF
  simpa only [Complex.reCLM_apply, Function.comp_def] using h

/-- A complex smooth representative of a real locally integrable function
induces the same real distribution after taking its real part. -/
theorem ae_eq_realPart_of_complex_test_integrals {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [MeasureSpace E] [BorelSpace E]
    [IsLocallyFiniteMeasure (volume : Measure E)]
    {V : Set E} (hV : IsOpen V) (v : E → ℝ) (F : E → ℂ)
    (hv : LocallyIntegrableOn v V volume)
    (hF : ContDiffOn ℝ (⊤ : ℕ∞) F V)
    (hRep : ∀ φ : E → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
      tsupport φ ⊆ V →
        ∫ x in V, (φ x : ℂ) * F x = ∫ x in V, (φ x : ℂ) * (v x : ℂ)) :
    ∀ᵐ x ∂volume, x ∈ V → v x = (F x).re := by
  have hFLoc : LocallyIntegrableOn F V volume :=
    hF.continuousOn.locallyIntegrableOn hV.measurableSet
  have hRealTest : ∀ φ : E → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
      tsupport φ ⊆ V → ∫ x in V, v x * φ x = ∫ x in V, (F x).re * φ x := by
    intro φ hφ hcompact hsupport
    have hvK : IntegrableOn v (tsupport φ) volume :=
      (hv.mono_set hsupport).integrableOn_isCompact hcompact
    have hvProdK : IntegrableOn (fun x => φ x * v x) (tsupport φ) volume := by
      simpa [mul_comm] using hvK.mul_continuousOn hφ.continuous.continuousOn hcompact
    have hvsup : support (fun x => φ x * v x) ⊆ tsupport φ := by
      exact (support_mul_subset_left _ _).trans (subset_tsupport φ)
    have hvProd : Integrable (fun x => φ x * v x) volume :=
      (integrableOn_iff_integrable_of_support_subset hvsup).mp hvProdK
    have hvProdV : IntegrableOn (fun x => φ x * v x) V volume := hvProd.integrableOn
    have hFK : IntegrableOn F (tsupport φ) volume :=
      (hFLoc.mono_set hsupport).integrableOn_isCompact hcompact
    have hφComplex : ContinuousOn (fun x => (φ x : ℂ)) (tsupport φ) :=
      (Complex.continuous_ofReal.comp hφ.continuous).continuousOn
    have hFProdK : IntegrableOn (fun x => (φ x : ℂ) * F x) (tsupport φ) volume := by
      simpa [mul_comm] using hFK.mul_continuousOn hφComplex hcompact
    have hFsup : support (fun x => (φ x : ℂ) * F x) ⊆ tsupport φ := by
      intro x hx
      have hxφComplex : (φ x : ℂ) ≠ 0 :=
        support_mul_subset_left (fun x => (φ x : ℂ)) F hx
      have hxφ : φ x ≠ 0 := by exact_mod_cast hxφComplex
      exact subset_tsupport φ (mem_support.mpr hxφ)
    have hFProd : Integrable (fun x => (φ x : ℂ) * F x) volume :=
      (integrableOn_iff_integrable_of_support_subset hFsup).mp hFProdK
    have hFProdV : IntegrableOn (fun x => (φ x : ℂ) * F x) V volume := hFProd.integrableOn
    have hComplexRealProd : IntegrableOn (fun x => ((φ x * v x : ℝ) : ℂ)) V volume := by
      have hcast : Integrable (fun x => ((φ x * v x : ℝ) : ℂ)) volume :=
        (@RCLike.ofRealLI ℂ _).toContinuousLinearMap.integrable_comp hvProd
      exact hcast.integrableOn
    have hComplexRep := hRep φ hφ hcompact hsupport
    have hComplexRight :
        (fun x => (φ x : ℂ) * (v x : ℂ)) = fun x => ((φ x * v x : ℝ) : ℂ) := by
      funext x
      simp [Complex.ofReal_mul]
    have hComplexRep' := hComplexRep
    rw [hComplexRight] at hComplexRep'
    have hReRep := congrArg Complex.re hComplexRep'
    have hFRe :
        ∫ x in V, ((φ x : ℂ) * F x).re = Complex.re (∫ x in V, (φ x : ℂ) * F x) :=
      integral_re hFProdV
    have hRealRe :
        ∫ x in V, (((φ x * v x : ℝ) : ℂ)).re =
          Complex.re (∫ x in V, ((φ x * v x : ℝ) : ℂ)) :=
      integral_re hComplexRealProd
    rw [← hFRe, ← hRealRe] at hReRep
    have hReLeft :
        (fun x => ((φ x : ℂ) * F x).re) = fun x => φ x * (F x).re := by
      funext x
      simp [Complex.mul_re]
    have hReRight :
        (fun x => (((φ x * v x : ℝ) : ℂ)).re) = fun x => φ x * v x := by
      funext x
      simp
    rw [hReLeft, hReRight] at hReRep
    simpa [mul_comm] using hReRep.symm
  exact ae_eq_of_open_test_integrals hV v (fun x => (F x).re) hv
    (realPart_contDiffOn F hF) hRealTest

end Hormander.F
