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

/-- The source's two endpoint densities with the same positive frame
normalization and compact uniform bounds. All objects are the actual
canonical chart Jacobians, not separate density candidates. -/
def DensityProperties (C : CanonicalFrameChartData Ω Y x) : Prop :=
    ∃ c : (Fin N → ℝ) → ℝ,
      ∃ wp wm : ((Fin N → ℝ) × (Fin N → ℝ)) → ℝ,
      ∃ lo hi B : ℝ, 0 < lo ∧ 0 < hi ∧ 0 < B ∧
        ContDiffOn ℝ (⊤ : ℕ∞) c (ball x C.radius) ∧
        (∀ η ∈ ball x C.radius, 0 < c η ∧ c η = |(frameValueCLM Y η).det|) ∧
        ContDiffOn ℝ (⊤ : ℕ∞) wp (ball x C.radius ×ˢ ball 0 C.radius) ∧
        ContDiffOn ℝ (⊤ : ℕ∞) wm (ball x C.radius ×ˢ ball 0 C.radius) ∧
        (∀ η ∈ ball x C.radius, wp (η,0) = 0 ∧ wm (η,0) = 0) ∧
        (∀ q, wm q = wp (q.1,-q.2)) ∧
        (∀ q ∈ ball x C.radius ×ˢ ball 0 C.radius,
          C.forwardDensity q = c q.1 * (1 + wp q) ∧
          C.firstVariableDensity q = c q.1 * (1 + wm q)) ∧
        (∀ η ∈ closedBall x (C.radius/2), lo ≤ c η ∧ c η ≤ hi) ∧
        (∀ η ∈ closedBall x (C.radius/2), ∀ u ∈ closedBall 0 (C.radius/2),
          |wp (η,u)| ≤ B * ‖u‖ ∧ |wm (η,u)| ≤ B * ‖u‖)

/-- One actual positive
frame normalization supplies both endpoint densities, with smooth
remainders related by coordinate negation and common compact bounds
(BB Proposition 10.33, pp. 512–513, corrected to absolute determinants). -/
theorem common_density_package (C : CanonicalFrameChartData Ω Y x)
    (hΩ : IsOpen Ω) (hY : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (Y i) Ω) :
    C.DensityProperties := by
  obtain ⟨c,wp,B,hB,hc,hcp,hwp,hzero,hfactor,hbound⟩ := C.forward_density_normalized_remainder
  obtain ⟨lo,hi,hlo,hhi,hcbound⟩ := C.forward_origin_density_compact_bounds
  let A := fun q : (Fin N → ℝ) × (Fin N → ℝ) => (q.1,-q.2)
  let wm := wp ∘ A
  have hA : ContDiffOn ℝ (⊤ : ℕ∞) A (ball x C.radius ×ˢ ball 0 C.radius) :=
    contDiffOn_fst.prodMk contDiffOn_snd.neg
  have hm : MapsTo A (ball x C.radius ×ˢ ball 0 C.radius)
      (ball x C.radius ×ˢ ball 0 C.radius) := by
    intro q hq
    exact ⟨hq.1, by simpa only [A, mem_ball_zero_iff, norm_neg] using hq.2⟩
  refine ⟨c,wp,wm,lo,hi,B,hlo,hhi,hB,hc,?_,hwp,hwp.comp hA hm,?_,?_,?_,?_,?_⟩
  · intro η hη
    refine ⟨hcp η hη, ?_⟩
    exact (hzero η hη).2.trans (C.forward_abs_jacobian_zero hΩ hY η hη)
  · intro η hη
    exact ⟨(hzero η hη).1, by simpa only [wm, Function.comp_apply, A, neg_zero] using (hzero η hη).1⟩
  · intro q
    rfl
  · intro q hq
    refine ⟨hfactor q hq, ?_⟩
    calc
      C.firstVariableDensity q = C.forwardDensity (A q) := C.firstVariableDensity_eq q hq
      _ = c q.1 * (1 + wm q) := hfactor (A q) (hm hq)
  · intro η hη
    have hsub : closedBall x (C.radius/2) ⊆ ball x C.radius :=
      closedBall_subset_ball (by linarith [C.radius_pos])
    rw [(hzero η (hsub hη)).2]
    exact hcbound η hη
  · intro η hη u hu
    have hnu : -u ∈ closedBall 0 (C.radius/2) := by
      simpa only [mem_closedBall_zero_iff, norm_neg] using hu
    exact ⟨hbound η hη u hu, by
      simpa only [wm, Function.comp_apply, A, norm_neg] using hbound η hη (-u) hnu⟩
end CanonicalFrameChartData
end RothschildStein.L1
