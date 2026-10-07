-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.Distribution.LocalizedSobolevStart
public import RothschildStein.S.TestOperators

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public section
noncomputable section
open Set TopologicalSpace SchwartzMap
namespace RothschildStein.Distribution
variable {N : ℕ}

/-- real cutoff multiplication agrees exactly
with localization by the product cutoff. -/
theorem localizedTempered_mul (U : Opens (Fin N → ℝ))
    (χ : TestFunction U ℝ (⊤ : ℕ∞)) (T : Distribution U ℂ (⊤ : ℕ∞))
    (ζ : (Fin N → ℝ) → ℝ) (hζ : ContDiff ℝ (⊤ : ℕ∞) ζ)
    (hg : (fun x => (ζ x : ℂ)).HasTemperateGrowth) :
    TemperedDistribution.smulLeftCLM ℂ (fun x => (ζ x : ℂ)) (localizedTempered U χ T) =
      localizedTempered U (testMultiplierOn U ζ hζ.contDiffOn χ) T := by
  ext φ
  rw [TemperedDistribution.smulLeftCLM_apply_apply, localizedTempered_apply, localizedTempered_apply]
  have he (L : ℂ →L[ℝ] ℝ) (hL : ∀ a b : ℝ, ∀ z : ℂ, L ((a : ℂ) * z) * b = L z * (b * a)) :
      S.schwartzCutoffTestCLM U χ (SchwartzMap.postcompCLM L
        (SchwartzMap.smulLeftCLM ℂ (fun x => (ζ x : ℂ)) φ)) =
      S.schwartzCutoffTestCLM U (testMultiplierOn U ζ hζ.contDiffOn χ)
        (SchwartzMap.postcompCLM L φ) := by
    ext x
    change L ((SchwartzMap.smulLeftCLM ℂ (fun x => (ζ x : ℂ)) φ) x) * χ x =
      L (φ x) * (χ x * ζ x)
    rw [SchwartzMap.smulLeftCLM_apply_apply hg]
    exact hL (ζ x) (χ x) (φ x)
  rw [he Complex.reCLM (by intros; simp; ring), he Complex.imCLM (by intros; simp; ring)]

/-- cutoff multiplication commutes with the existing
coordinate transfer, so the localized Sobolev start applies to ζ′v. -/
theorem localizedTemperedEuclidean_mul (U : Opens (Fin N → ℝ))
    (χ : TestFunction U ℝ (⊤ : ℕ∞)) (T : Distribution U ℂ (⊤ : ℕ∞))
    (ζ : (Fin N → ℝ) → ℝ) (hζ : ContDiff ℝ (⊤ : ℕ∞) ζ)
    (hg : (fun x => (ζ x : ℂ)).HasTemperateGrowth)
    (hge : (fun x : Hormander.A.Carrier N => (ζ ((Hormander.F.coordinateEquiv N).symm x) : ℂ)).HasTemperateGrowth) :
    TemperedDistribution.smulLeftCLM ℂ
      (fun x : Hormander.A.Carrier N => (ζ ((Hormander.F.coordinateEquiv N).symm x) : ℂ))
      (localizedTemperedEuclidean U χ T) =
      localizedTemperedEuclidean U (testMultiplierOn U ζ hζ.contDiffOn χ) T := by
  have he := localizedTempered_mul U χ T ζ hζ hg
  ext φ
  have hp : Hormander.F.schwartzToCoordinatesCLM N
      (SchwartzMap.smulLeftCLM ℂ
        (fun x : Hormander.A.Carrier N => (ζ ((Hormander.F.coordinateEquiv N).symm x) : ℂ)) φ) =
      SchwartzMap.smulLeftCLM ℂ (fun x => (ζ x : ℂ))
        (Hormander.F.schwartzToCoordinatesCLM N φ) := by
    ext x
    simp only [Hormander.F.schwartzToCoordinatesCLM, SchwartzMap.compCLMOfContinuousLinearEquiv_apply]
    change (SchwartzMap.smulLeftCLM ℂ _ φ) (Hormander.F.coordinateEquiv N x) = _
    rw [SchwartzMap.smulLeftCLM_apply_apply hge, SchwartzMap.smulLeftCLM_apply_apply hg]
    simp
  change localizedTempered U χ T
    (Hormander.F.schwartzToCoordinatesCLM N (SchwartzMap.smulLeftCLM ℂ _ φ)) = _
  rw [hp]
  exact congrArg (fun v => v (Hormander.F.schwartzToCoordinatesCLM N φ)) he

end RothschildStein.Distribution
