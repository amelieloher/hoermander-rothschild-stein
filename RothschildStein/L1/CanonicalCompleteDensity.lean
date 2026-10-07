-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module
public import RothschildStein.L1.CanonicalFirstDensityRemainder
public import RothschildStein.L1.CanonicalDensityFactorBounds
public import RothschildStein.L1.CanonicalForwardDerivativeZero
@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set Metric
namespace RothschildStein.L1
namespace CanonicalFrameChartData
variable {N : ℕ} {Ω : Set (Fin N → ℝ)}
variable {Y : Fin N → (Fin N → ℝ) → (Fin N → ℝ)} {x : Fin N → ℝ}

/-- A positive normalized Jacobian with its exact frame normalization,
smooth coefficients and uniform bounds on the smaller coefficient patch. -/
def PositiveDensityProperties (C : CanonicalFrameChartData Ω Y x)
    (J : ((Fin N → ℝ) × (Fin N → ℝ)) → ℝ) : Prop :=
  ∃ c : (Fin N → ℝ) → ℝ, ∃ w : ((Fin N → ℝ) × (Fin N → ℝ)) → ℝ,
    ∃ B lo hi : ℝ, 0 < B ∧ 0 < lo ∧ 0 < hi ∧
      ContDiffOn ℝ (⊤ : ℕ∞) c (ball x C.radius) ∧
      (∀ η ∈ ball x C.radius, 0 < c η ∧ c η = |(frameValueCLM Y η).det|) ∧
      ContDiffOn ℝ (⊤ : ℕ∞) w (ball x C.radius ×ˢ ball 0 C.radius) ∧
      (∀ η ∈ ball x C.radius, w (η,0) = 0) ∧
      (∀ q ∈ ball x C.radius ×ˢ ball 0 C.radius, J q = c q.1 * (1 + w q)) ∧
      (∀ η ∈ closedBall x (C.radius/2), lo ≤ c η ∧ c η ≤ hi) ∧
      (∀ η ∈ closedBall x (C.radius/2), ∀ u ∈ closedBall 0 (C.radius/2),
        |w (η,u)| ≤ B * ‖u‖)

/-- The forward Lebesgue Jacobian satisfies the complete positive density
conditions, including identification of its normalization with the frame
(BB Proposition 10.33, pp. 512–513). -/
theorem forward_positive_density_properties (C : CanonicalFrameChartData Ω Y x)
    (hΩ : IsOpen Ω) (hY : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (Y i) Ω) :
    C.PositiveDensityProperties C.forwardDensity := by
  obtain ⟨c,w,B,hB,hc,hcp,hw,hw0,hfactor,hbound⟩ := C.forward_density_normalized_remainder
  obtain ⟨lo,hi,hlo,hhi,hcb⟩ := C.forward_origin_density_compact_bounds
  refine ⟨c,w,B,lo,hi,hB,hlo,hhi,hc,?_,hw,fun η hη => (hw0 η hη).1,hfactor,?_,hbound⟩
  · intro η hη
    refine ⟨hcp η hη,?_⟩
    rw [(hw0 η hη).2]
    exact C.forward_abs_jacobian_zero hΩ hY η hη
  · intro η hη
    have hh : η ∈ ball x C.radius :=
      (closedBall_subset_ball (by linarith [C.radius_pos])) hη
    rw [(hw0 η hh).2]
    exact hcb η hη

/-- The first-variable Lebesgue Jacobian has the same exact positive
frame normalization and compact smaller-patch bounds
(BB Proposition 10.33, pp. 512–513). -/
theorem first_positive_density_properties (C : CanonicalFrameChartData Ω Y x)
    (hΩ : IsOpen Ω) (hY : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (Y i) Ω) :
    C.PositiveDensityProperties C.firstVariableDensity := by
  obtain ⟨c,w,B,hB,hc,hcp,hw,hw0,hfactor,hbound⟩ := C.first_density_normalized_remainder
  obtain ⟨lo,hi,hlo,hhi,hcb⟩ := C.forward_origin_density_compact_bounds
  have hzero (η : Fin N → ℝ) (hη : η ∈ ball x C.radius) :
      C.firstVariableDensity (η,0) = C.forwardDensity (η,0) := by
    rw [C.firstVariableDensity_eq (η,0) ⟨hη,mem_ball_self C.radius_pos⟩]
    simp only [neg_zero]
  refine ⟨c,w,B,lo,hi,hB,hlo,hhi,hc,?_,hw,fun η hη => (hw0 η hη).1,hfactor,?_,hbound⟩
  · intro η hη
    refine ⟨hcp η hη,?_⟩
    rw [(hw0 η hη).2,hzero η hη]
    exact C.forward_abs_jacobian_zero hΩ hY η hη
  · intro η hη
    have hh : η ∈ ball x C.radius :=
      (closedBall_subset_ball (by linarith [C.radius_pos])) hη
    rw [(hw0 η hh).2,hzero η hh]
    exact hcb η hη
end CanonicalFrameChartData
end RothschildStein.L1
