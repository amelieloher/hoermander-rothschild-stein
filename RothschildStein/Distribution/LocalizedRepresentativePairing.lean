-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.Distribution.LocalizedTestPairing

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public section
noncomputable section
open Set MeasureTheory TopologicalSpace SchwartzMap
namespace RothschildStein.Distribution

/-- an actual smooth localized tempered
representative gives the original distribution pairing on every real
compact test in the plateau region, with exact coordinate transport. -/
theorem localizedRepresentative_on_realTest {N : ℕ}
    (Ω : Opens (Fin N → ℝ)) (χ ψ : TestFunction Ω ℝ (⊤ : ℕ∞))
    (T : Distribution Ω ℂ (⊤ : ℕ∞)) (ζ : Hormander.A.Carrier N → ℝ)
    (hζg : (fun y => (ζ y : ℂ)).HasTemperateGrowth)
    (hχ : ∀ x ∈ tsupport ψ, χ x = 1)
    (hζ : ∀ x ∈ tsupport ψ, ζ (Hormander.F.coordinateEquiv N x) = 1)
    (F : Hormander.A.Carrier N → ℂ)
    (hrep : ∀ φ : SchwartzMap (Hormander.A.Carrier N) ℂ,
      TemperedDistribution.smulLeftCLM ℂ (fun y => (ζ y : ℂ))
        (localizedTemperedEuclidean Ω χ T) φ = ∫ y, φ y * F y) :
    T ψ = ∫ x, ψ x • F (Hormander.F.coordinateEquiv N x) := by
  let φ := Hormander.F.schwartzToEuclideanCLM N
    (SchwartzMap.postcompCLM Complex.ofRealCLM (ψ.hasCompactSupport.toSchwartzMap ψ.contDiff))
  have hm : SchwartzMap.smulLeftCLM ℂ (fun y => (ζ y : ℂ)) φ = φ := by
    ext y
    rw [SchwartzMap.smulLeftCLM_apply_apply hζg]
    change (ζ y : ℂ) • (ψ ((Hormander.F.coordinateEquiv N).symm y) : ℂ) =
      (ψ ((Hormander.F.coordinateEquiv N).symm y) : ℂ)
    by_cases hx : (Hormander.F.coordinateEquiv N).symm y ∈ tsupport ψ
    · have hz : ζ y = 1 := by
        simpa only [ContinuousLinearEquiv.apply_symm_apply] using
          hζ ((Hormander.F.coordinateEquiv N).symm y) hx
      rw [hz]
      simp
    · rw [image_eq_zero_of_notMem_tsupport hx]
      simp
  have he := hrep φ
  rw [TemperedDistribution.smulLeftCLM_apply_apply, hm] at he
  rw [localizedTemperedEuclidean_on_realTest Ω χ ψ T hχ] at he
  rw [← Hormander.F.integral_comp_coordinateEquiv] at he
  exact he.trans (integral_congr_ae (Filter.Eventually.of_forall (fun x => by
    change (ψ ((Hormander.F.coordinateEquiv N).symm (Hormander.F.coordinateEquiv N x)) : ℂ) *
      F (Hormander.F.coordinateEquiv N x) = ψ x • F (Hormander.F.coordinateEquiv N x)
    rw [ContinuousLinearEquiv.symm_apply_apply, Complex.real_smul])))

end RothschildStein.Distribution
