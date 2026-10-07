-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.Distribution.AdjointTest
public import RothschildStein.Distribution.LocalizedTempered

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public section
noncomputable section
open Set TopologicalSpace SchwartzMap
namespace RothschildStein.Distribution

/-- an actual distribution equation on real tests
transfers to localized complex tempered distributions. The forcing
may itself be any distribution; smooth forcing is a specialization. -/
theorem localized_forcing_of_distributionEquation {k N : ℕ}
    (Ω : Opens (Fin N → ℝ))
    (Y : Fin (k + 1) → (Fin N → ℝ) → (Fin N → ℝ)) (c : (Fin N → ℝ) → ℝ)
    (hY : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (Y i) (Ω : Set (Fin N → ℝ)))
    (hcΩ : ContDiffOn ℝ (⊤ : ℕ∞) c (Ω : Set (Fin N → ℝ)))
    (hX : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (Hormander.F.pushVectorFields Y i))
    (hXc : ∀ i, HasCompactSupport (Hormander.F.pushVectorFields Y i))
    (hc : ContDiff ℝ (⊤ : ℕ∞) (fun y => c ((Hormander.F.coordinateEquiv N).symm y)))
    (hcc : HasCompactSupport (fun y => c ((Hormander.F.coordinateEquiv N).symm y)))
    (χ ζ : TestFunction Ω ℝ (⊤ : ℕ∞))
    (hχ : ∀ x ∈ tsupport ζ, χ x = 1)
    (hζ : (fun y : Hormander.A.Carrier N => (ζ ((Hormander.F.coordinateEquiv N).symm y) : ℂ)).HasTemperateGrowth)
    (T G : Distribution Ω ℂ (⊤ : ℕ∞))
    (heq : ∀ ψ : TestFunction Ω ℝ (⊤ : ℕ∞), T (adjointTest Ω Y c hY hcΩ ψ) = G ψ) :
    TemperedDistribution.smulLeftCLM ℂ
      (fun y : Hormander.A.Carrier N => (ζ ((Hormander.F.coordinateEquiv N).symm y) : ℂ))
      (Hormander.hormanderOp (Hormander.F.pushVectorFields Y)
        (fun y => c ((Hormander.F.coordinateEquiv N).symm y))
        (localizedTemperedEuclidean Ω χ T)) = localizedTemperedEuclidean Ω ζ G := by
  ext φ
  let Φ := SchwartzMap.smulLeftCLM ℂ
    (fun y : Hormander.A.Carrier N => (ζ ((Hormander.F.coordinateEquiv N).symm y) : ℂ)) φ
  let A := Hormander.F.hormanderTransposeSchwartz (Hormander.F.pushVectorFields Y)
    (fun y => c ((Hormander.F.coordinateEquiv N).symm y)) Φ
  let ψ (L : ℂ →L[ℝ] ℝ) := S.schwartzCutoffTestCLM Ω ζ
    (SchwartzMap.postcompCLM L (Hormander.F.schwartzToCoordinatesCLM N φ))
  have htest (L : ℂ →L[ℝ] ℝ)
      (hscale : ∀ a : ℝ, ∀ z : ℂ, L ((a : ℂ) * z) = a * L z)
      (htranspose : ∀ y, L (A y) = Hormander.F.euclideanAdjointTest₂
        (Hormander.F.pushVectorFields Y) (fun y => c ((Hormander.F.coordinateEquiv N).symm y))
        (fun y => L (Φ y)) y) :
      S.schwartzCutoffTestCLM Ω χ
        (SchwartzMap.postcompCLM L (Hormander.F.schwartzToCoordinatesCLM N A)) =
        adjointTest Ω Y c hY hcΩ (ψ L) := by
    have hφ : (fun y => L (Φ y)) =
        fun y => ψ L ((Hormander.F.coordinateEquiv N).symm y) := by
      funext y
      change L ((SchwartzMap.smulLeftCLM ℂ _ φ) y) =
        L (φ (Hormander.F.coordinateEquiv N ((Hormander.F.coordinateEquiv N).symm y))) *
          ζ ((Hormander.F.coordinateEquiv N).symm y)
      rw [SchwartzMap.smulLeftCLM_apply_apply hζ, smul_eq_mul, hscale]
      simp only [ContinuousLinearEquiv.apply_symm_apply]
      ring
    have hs : tsupport (ψ L) ⊆ tsupport ζ := by
      change tsupport (fun x => L (φ (Hormander.F.coordinateEquiv N x)) * ζ x) ⊆ tsupport ζ
      exact tsupport_mul_subset_right
    ext x
    change L (A (Hormander.F.coordinateEquiv N x)) * χ x =
      Hormander.Interface.hormanderAdjointTest Y c (ψ L) x
    rw [htranspose, hφ, Hormander.F.hormanderAdjointTest_coordinateConjugate]
    by_cases hx : x ∈ tsupport ζ
    · rw [hχ x hx, mul_one]
    · have hz : Hormander.Interface.hormanderAdjointTest Y c (ψ L) x = 0 := by
        apply image_eq_zero_of_notMem_tsupport
        exact fun h => hx ((Hormander.F.hormanderAdjointTest_tsupport_subset Y c (ψ L)).trans hs h)
      rw [hz, zero_mul]
  have hr := htest Complex.reCLM (by intros; simp)
    (fun y => Hormander.F.hormanderTransposeSchwartz_re _ _ hX hXc hc hcc Φ y)
  have hi := htest Complex.imCLM (by intros; simp)
    (fun y => Hormander.F.hormanderTransposeSchwartz_im _ _ hX hXc hc hcc Φ y)
  rw [TemperedDistribution.smulLeftCLM_apply_apply, Hormander.F.hormanderOp_apply_transpose]
  change localizedTempered Ω χ T (Hormander.F.schwartzToCoordinatesCLM N A) =
    localizedTempered Ω ζ G (Hormander.F.schwartzToCoordinatesCLM N φ)
  rw [localizedTempered_apply, localizedTempered_apply, hr, hi, heq, heq]

end RothschildStein.Distribution
