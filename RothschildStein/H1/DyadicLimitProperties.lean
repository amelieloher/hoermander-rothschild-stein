-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H1.DyadicLimit
public import RothschildStein.H1.LocalDilationIntegrability

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
open Set MeasureTheory Filter
namespace RothschildStein.H1
variable {N : ℕ} (G : HomogeneousGroup N)

/-- The global dyadic candidate is locally integrable when
its local kernel is, since the correction is globally smooth (BB p. 266). -/
theorem locallyIntegrable_fundamentalDyadicLimit
    (hQ : 2 < (G.homogeneousDimension : ℝ))
    {Γ ω : (Fin N → ℝ) → ℝ} (hΓ : LocallyIntegrable Γ)
    (hω : ContDiff ℝ (⊤ : ℕ∞) ω) (hs : HasCompactSupport ω) :
    LocallyIntegrable (fundamentalDyadicLimit G Γ ω) := by
  have h := contDiff_fundamentalCorrectionSeries G hQ hω hs
  exact hΓ.add h.continuous.locallyIntegrable

/-- The correction does not change smoothness off the origin
(BB p. 266). -/
theorem contDiffOn_fundamentalDyadicLimit
    (hQ : 2 < (G.homogeneousDimension : ℝ))
    {Γ ω : (Fin N → ℝ) → ℝ} (hΓ : ContDiffOn ℝ (⊤ : ℕ∞) Γ {x | x ≠ 0})
    (hω : ContDiff ℝ (⊤ : ℕ∞) ω) (hs : HasCompactSupport ω) :
    ContDiffOn ℝ (⊤ : ℕ∞) (fundamentalDyadicLimit G Γ ω) {x | x ≠ 0} := by
  exact hΓ.add (contDiff_fundamentalCorrectionSeries G hQ hω hs).contDiffOn

/-- Dyadic homogeneity follows from the exact consecutive
scaled-kernel covariance and the uniform limit (BB p. 266). -/
theorem fundamentalDyadicLimit_dyadic
    (hQ : 2 < (G.homogeneousDimension : ℝ))
    {Γ ω : (Fin N → ℝ) → ℝ} (hsm : ContDiff ℝ (⊤ : ℕ∞) ω)
    (hs : HasCompactSupport ω)
    (hω : ∀ x ≠ 0, ω x = scaledFundamentalKernel G 2 Γ x - Γ x)
    {x : Fin N → ℝ} (hx : x ≠ 0) :
    fundamentalDyadicLimit G Γ ω (G.dilate 2 x) =
      (2 : ℝ) ^ (2 - (G.homogeneousDimension : ℝ)) * fundamentalDyadicLimit G Γ ω x := by
  have hz : G.dilate 2 x ≠ 0 := by
    intro hz
    exact hx ((G2.dilate_bijective G (by norm_num : (2 : ℝ) ≠ 0)).injective
      (hz.trans (G2.dilate_zero G _).symm))
  have hu := tendstoUniformlyOn_scaledFundamentalKernel G hQ hsm hs hω
  have hleft := (hu.tendsto_at hz).comp (tendsto_add_atTop_nat 1)
  have hright := (hu.tendsto_at hx).const_mul
    ((2 : ℝ) ^ (2 - (G.homogeneousDimension : ℝ)))
  have he : (fun n : ℕ => scaledFundamentalKernel G ((2 : ℝ) ^ (n + 1)) Γ
      (G.dilate 2 x)) = (fun n : ℕ =>
      (2 : ℝ) ^ (2 - (G.homogeneousDimension : ℝ)) *
        scaledFundamentalKernel G ((2 : ℝ) ^ n) Γ x) := by
    funext n
    exact scaledFundamentalKernel_dyadic_step G Γ n x
  change Tendsto (fun n : ℕ => scaledFundamentalKernel G ((2 : ℝ) ^ (n + 1)) Γ
    (G.dilate 2 x)) atTop _ at hleft
  rw [he] at hleft
  exact tendsto_nhds_unique hleft hright

end RothschildStein.H1
