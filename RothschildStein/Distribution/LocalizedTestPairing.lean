-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.Distribution.LocalizedTempered

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public section
noncomputable section
open Set TopologicalSpace SchwartzMap
namespace RothschildStein.Distribution
variable {N : ℕ}

/-- the complexified localized distribution retains
its exact action on real compact tests where the cutoff is one. -/
theorem localizedTempered_on_realTest (U : Opens (Fin N → ℝ))
    (χ ψ : TestFunction U ℝ (⊤ : ℕ∞)) (T : Distribution U ℂ (⊤ : ℕ∞))
    (hχ : ∀ x ∈ tsupport ψ, χ x = 1) :
    localizedTempered U χ T
      (SchwartzMap.postcompCLM Complex.ofRealCLM
        (ψ.hasCompactSupport.toSchwartzMap ψ.contDiff)) = T ψ := by
  rw [localizedTempered_apply]
  have hr : S.schwartzCutoffTestCLM U χ
      (SchwartzMap.postcompCLM Complex.reCLM
        (SchwartzMap.postcompCLM Complex.ofRealCLM
          (ψ.hasCompactSupport.toSchwartzMap ψ.contDiff))) = ψ := by
    ext x
    change (ψ x : ℂ).re * χ x = ψ x
    simp only [Complex.ofReal_re]
    by_cases hx : x ∈ tsupport ψ
    · rw [hχ x hx, mul_one]
    · rw [image_eq_zero_of_notMem_tsupport hx, zero_mul]
  have hi : S.schwartzCutoffTestCLM U χ
      (SchwartzMap.postcompCLM Complex.imCLM
        (SchwartzMap.postcompCLM Complex.ofRealCLM
          (ψ.hasCompactSupport.toSchwartzMap ψ.contDiff))) = 0 := by
    ext x
    change (ψ x : ℂ).im * χ x = 0
    simp
  rw [hr, hi, map_zero, mul_zero, add_zero]

/-- exact real-test pairing survives the existing
Euclidean transfer; it introduces no scalar or Jacobian factor. -/
theorem localizedTemperedEuclidean_on_realTest (U : Opens (Fin N → ℝ))
    (χ ψ : TestFunction U ℝ (⊤ : ℕ∞)) (T : Distribution U ℂ (⊤ : ℕ∞))
    (hχ : ∀ x ∈ tsupport ψ, χ x = 1) :
    localizedTemperedEuclidean U χ T
      (Hormander.F.schwartzToEuclideanCLM N
        (SchwartzMap.postcompCLM Complex.ofRealCLM
          (ψ.hasCompactSupport.toSchwartzMap ψ.contDiff))) = T ψ := by
  have he (φ : SchwartzMap (Fin N → ℝ) ℂ) :
      Hormander.F.schwartzToCoordinatesCLM N (Hormander.F.schwartzToEuclideanCLM N φ) = φ := by
    ext x
    simp [Hormander.F.schwartzToCoordinatesCLM, Hormander.F.schwartzToEuclideanCLM]
  change localizedTempered U χ T (Hormander.F.schwartzToCoordinatesCLM N _) = T ψ
  rw [he]
  exact localizedTempered_on_realTest U χ ψ T hχ

end RothschildStein.Distribution
