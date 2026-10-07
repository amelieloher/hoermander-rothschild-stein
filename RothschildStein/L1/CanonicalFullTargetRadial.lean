-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.L1.CanonicalCommonSourceChart

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set Metric
open scoped BigOperators
namespace RothschildStein.L1.CanonicalFrameChartData

/-- Every point in the entire
canonical image has the actual radial trajectory in the original
spatial domain, including both time endpoints. -/
theorem full_target_radial_curve {N : ℕ} {Ω : Set (Fin N → ℝ)}
    {Y : Fin N → (Fin N → ℝ) → (Fin N → ℝ)} {x : Fin N → ℝ}
    (C : CanonicalFrameChartData Ω Y x) {U : Set (Fin N → ℝ)}
    (hsub : U ⊆ ball x C.radius)
    (hsmall : ∀ η ∈ U, ∀ ξ ∈ U, C.theta (η,ξ) ∈ ball 0 C.radius)
    {η u : Fin N → ℝ} (hη : η ∈ U)
    (hu : u ∈ (fun ξ => C.theta (η,ξ)) '' U) :
    ∃ γ : ℝ → (Fin N → ℝ), γ 0 = η ∧
      γ 1 = canonicalFrameMap C.time C.flow (η,u) ∧
      ∀ t ∈ Icc (0 : ℝ) 1, γ t ∈ Ω ∧
        HasDerivAt γ (∑ j, u j • Y j (γ t)) t := by
  obtain ⟨ξ,hξ,rfl⟩ := hu
  have hcoef := hsmall η hη ξ hξ
  refine ⟨C.exponentialCurve η (C.theta (η,ξ)),
    C.exponentialCurve_zero η _ (hsub hη) hcoef,
    C.exponentialCurve_one η _,?_⟩
  intro t ht
  have htime : C.time*t ∈ Ioo (-C.timeRadius) C.timeRadius := by
    constructor
    · have hnonneg := mul_nonneg C.time_pos.le ht.1
      linarith [C.timeRadius_pos]
    · have hle := mul_le_mul_of_nonneg_left ht.2 C.time_pos.le
      linarith [C.time_lt]
  exact ⟨C.exponentialCurve_mem η _ (hsub hη) hcoef htime,
    C.exponentialCurve_hasDerivAt η _ (hsub hη) hcoef htime⟩

end RothschildStein.L1.CanonicalFrameChartData
