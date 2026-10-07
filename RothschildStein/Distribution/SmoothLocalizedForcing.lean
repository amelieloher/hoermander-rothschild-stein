-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.Distribution.LocalizedTempered
public import RothschildStein.S.TestOperators

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public section
noncomputable section
open Set MeasureTheory TopologicalSpace SchwartzMap
namespace RothschildStein.Distribution

/-- smooth complex forcing localized by an interior
real test is an actual Schwartz function, and its distribution is the
localized complexification of the original real-test distribution. -/
theorem exists_schwartz_localized_smoothForcing {N : ℕ}
    (Ω : Opens (Fin N → ℝ)) (ζ : TestFunction Ω ℝ (⊤ : ℕ∞))
    (g : (Fin N → ℝ) → ℂ)
    (hg : ContDiffOn ℝ (⊤ : ℕ∞) g (Ω : Set (Fin N → ℝ))) :
    ∃ f : SchwartzMap (Fin N → ℝ) ℂ,
      (∀ x, f x = (ζ x : ℂ) * g x) ∧
      localizedTempered Ω ζ (Distribution.ofFun Ω g volume (⊤ : ℕ∞)) =
        (f : TemperedDistribution (Fin N → ℝ) ℂ) := by
  let R := testMultiplierOn Ω (fun x => (g x).re) (Complex.reCLM.contDiff.comp_contDiffOn hg) ζ
  let I := testMultiplierOn Ω (fun x => (g x).im) (Complex.imCLM.contDiff.comp_contDiffOn hg) ζ
  let f := SchwartzMap.postcompCLM Complex.ofRealCLM (R.hasCompactSupport.toSchwartzMap R.contDiff) +
    Complex.I • SchwartzMap.postcompCLM Complex.ofRealCLM (I.hasCompactSupport.toSchwartzMap I.contDiff)
  have hf (x : Fin N → ℝ) : f x = (ζ x : ℂ) * g x := by
    change ((ζ x * (g x).re : ℝ) : ℂ) + Complex.I * ((ζ x * (g x).im : ℝ) : ℂ) = _
    simp only [Complex.ofReal_mul]
    conv_rhs => rw [← Complex.re_add_im (g x)]
    ring
  refine ⟨f, hf, ?_⟩
  have hgi : LocallyIntegrableOn g (Ω : Set (Fin N → ℝ)) volume :=
    hg.continuousOn.locallyIntegrableOn Ω.isOpen.measurableSet
  ext φ
  let ψR := S.schwartzCutoffTestCLM Ω ζ (SchwartzMap.postcompCLM Complex.reCLM φ)
  let ψI := S.schwartzCutoffTestCLM Ω ζ (SchwartzMap.postcompCLM Complex.imCLM φ)
  have hr := ψR.integrable_smul hgi
  have hi := ψI.integrable_smul hgi
  rw [localizedTempered_apply, Distribution.ofFun_apply hgi,
    Distribution.ofFun_apply hgi, SchwartzMap.coe_apply]
  change (∫ x, ψR x • g x) + Complex.I * (∫ x, ψI x • g x) = ∫ x, φ x • f x
  rw [← integral_const_mul, ← integral_add hr (hi.const_mul Complex.I)]
  apply integral_congr_ae
  filter_upwards [] with x
  change ((φ x).re * ζ x) • g x + Complex.I * (((φ x).im * ζ x) • g x) = φ x • f x
  rw [hf]
  simp only [Complex.real_smul, smul_eq_mul, Complex.ofReal_mul]
  conv_rhs => rw [← Complex.re_add_im (φ x)]
  ring

/-- the existing volume-preserving
coordinate map transports a Schwartz function's distribution exactly. -/
theorem temperedToEuclidean_coeSchwartz {N : ℕ} (f : SchwartzMap (Fin N → ℝ) ℂ) :
    Hormander.F.temperedToEuclideanCLM N (f : TemperedDistribution (Fin N → ℝ) ℂ) =
      (Hormander.F.schwartzToEuclideanCLM N f : TemperedDistribution (Hormander.A.Carrier N) ℂ) := by
  ext φ
  change (f : TemperedDistribution (Fin N → ℝ) ℂ) (Hormander.F.schwartzToCoordinatesCLM N φ) = _
  rw [SchwartzMap.coe_apply, SchwartzMap.coe_apply]
  rw [← Hormander.F.integral_comp_coordinateEquiv]
  apply integral_congr_ae
  filter_upwards [] with x
  change φ (Hormander.F.coordinateEquiv N x) • f x =
    φ (Hormander.F.coordinateEquiv N x) • f ((Hormander.F.coordinateEquiv N).symm (Hormander.F.coordinateEquiv N x))
  rw [ContinuousLinearEquiv.symm_apply_apply]

end RothschildStein.Distribution
