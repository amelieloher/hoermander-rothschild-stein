-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module
public import RothschildStein.L1.CanonicalFirstVariableDensity
@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set Metric
namespace RothschildStein.L1
namespace CanonicalFrameChartData
variable {N : ℕ} {Ω : Set (Fin N → ℝ)}
variable {Y : Fin N → (Fin N → ℝ) → (Fin N → ℝ)} {x : Fin N → ℝ}

/-- Negating the canonical coordinate
transports the positive normalization and uniform remainder bound to
the actual first-variable inverse Jacobian. -/
theorem first_density_normalized_remainder (C : CanonicalFrameChartData Ω Y x) :
    ∃ c : (Fin N → ℝ) → ℝ, ∃ w : ((Fin N → ℝ) × (Fin N → ℝ)) → ℝ, ∃ B : ℝ,
      0 < B ∧ ContDiffOn ℝ (⊤ : ℕ∞) c (ball x C.radius) ∧
      (∀ ξ ∈ ball x C.radius, 0 < c ξ) ∧
      ContDiffOn ℝ (⊤ : ℕ∞) w (ball x C.radius ×ˢ ball 0 C.radius) ∧
      (∀ ξ ∈ ball x C.radius, w (ξ,0) = 0 ∧ c ξ = C.firstVariableDensity (ξ,0)) ∧
      (∀ q ∈ ball x C.radius ×ˢ ball 0 C.radius,
        C.firstVariableDensity q = c q.1 * (1 + w q)) ∧
      (∀ ξ ∈ closedBall x (C.radius/2), ∀ u ∈ closedBall 0 (C.radius/2),
        |w (ξ,u)| ≤ B * ‖u‖) := by
  obtain ⟨c,w,B,hB,hc,hcp,hw,hw0,hfactor,hbound⟩ := C.forward_density_normalized_remainder
  let A := fun q : (Fin N → ℝ) × (Fin N → ℝ) => (q.1,-q.2)
  have hA : ContDiffOn ℝ (⊤ : ℕ∞) A (ball x C.radius ×ˢ ball 0 C.radius) :=
    contDiffOn_fst.prodMk contDiffOn_snd.neg
  have hm : MapsTo A (ball x C.radius ×ˢ ball 0 C.radius)
      (ball x C.radius ×ˢ ball 0 C.radius) := by
    intro q hq
    refine ⟨hq.1,?_⟩
    change -q.2 ∈ ball 0 C.radius
    simpa only [mem_ball_zero_iff,norm_neg] using hq.2
  refine ⟨c,w ∘ A,B,hB,hc,hcp,hw.comp hA hm,?_,?_,?_⟩
  · intro ξ hξ
    refine ⟨?_,?_⟩
    · simpa only [Function.comp_apply,A,neg_zero] using (hw0 ξ hξ).1
    · rw [C.firstVariableDensity_eq (ξ,0) ⟨hξ,mem_ball_self C.radius_pos⟩]
      simpa only [neg_zero] using (hw0 ξ hξ).2
  · intro q hq
    rw [C.firstVariableDensity_eq q hq,hfactor (A q) (hm hq)]
    rfl
  · intro ξ hξ u hu
    have hnu : -u ∈ closedBall 0 (C.radius/2) := by
      simpa only [mem_closedBall_zero_iff,norm_neg] using hu
    simpa only [Function.comp_apply,A,norm_neg] using hbound ξ hξ (-u) hnu
end CanonicalFrameChartData
end RothschildStein.L1
