-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module
public import RothschildStein.L1.CanonicalForwardJacobianSmooth
public import RothschildStein.L1.CompactParameterZeroBound
@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set Metric
namespace RothschildStein.L1
namespace CanonicalFrameChartData
variable {N : ℕ} {Ω : Set (Fin N → ℝ)}
variable {Y : Fin N → (Fin N → ℝ) → (Fin N → ℝ)} {x : Fin N → ℝ}

/-- The actual positive forward chart volume density. -/
def forwardDensity (C : CanonicalFrameChartData Ω Y x)
    (q : (Fin N → ℝ) × (Fin N → ℝ)) : ℝ :=
  |(fderiv ℝ (fun u => canonicalFrameMap C.time C.flow (q.1,u)) q.2).det|

/-- Normalize the actual positive Jacobian by its origin
value and obtain a jointly smooth, uniformly linear vanishing remainder. -/
theorem forward_density_normalized_remainder (C : CanonicalFrameChartData Ω Y x) :
    ∃ c : (Fin N → ℝ) → ℝ, ∃ w : ((Fin N → ℝ) × (Fin N → ℝ)) → ℝ, ∃ B : ℝ,
      0 < B ∧ ContDiffOn ℝ (⊤ : ℕ∞) c (ball x C.radius) ∧
      (∀ η ∈ ball x C.radius, 0 < c η) ∧
      ContDiffOn ℝ (⊤ : ℕ∞) w (ball x C.radius ×ˢ ball 0 C.radius) ∧
      (∀ η ∈ ball x C.radius, w (η,0) = 0 ∧ c η = C.forwardDensity (η,0)) ∧
      (∀ q ∈ ball x C.radius ×ˢ ball 0 C.radius,
        C.forwardDensity q = c q.1 * (1 + w q)) ∧
      (∀ η ∈ closedBall x (C.radius/2), ∀ u ∈ closedBall 0 (C.radius/2),
        |w (η,u)| ≤ B * ‖u‖) := by
  let c := fun η => C.forwardDensity (η,0)
  let w := fun q : (Fin N → ℝ) × (Fin N → ℝ) => C.forwardDensity q / c q.1 - 1
  have h0 : (0 : Fin N → ℝ) ∈ ball 0 C.radius := mem_ball_self C.radius_pos
  have hJ : ContDiffOn ℝ (⊤ : ℕ∞) C.forwardDensity
      (ball x C.radius ×ˢ ball 0 C.radius) := C.forward_abs_jacobian_contDiffOn
  have hc : ContDiffOn ℝ (⊤ : ℕ∞) c (ball x C.radius) :=
    hJ.comp (contDiffOn_id.prodMk contDiffOn_const) (fun η hη => ⟨hη,h0⟩)
  have hcp : ∀ η ∈ ball x C.radius, 0 < c η :=
    fun η hη => C.forward_abs_jacobian_pos η 0 hη h0
  have hw : ContDiffOn ℝ (⊤ : ℕ∞) w (ball x C.radius ×ˢ ball 0 C.radius) :=
    (hJ.div (hc.comp contDiffOn_fst (fun q hq => hq.1))
      (fun q hq => ne_of_gt (hcp q.1 hq.1))).sub contDiffOn_const
  have hw0 : ∀ η ∈ ball x C.radius, w (η,0) = 0 := by
    intro η hη
    change c η / c η - 1 = 0
    rw [div_self (ne_of_gt (hcp η hη)), sub_self]
  obtain ⟨B,hB,hbound⟩ := compact_parameter_zero_bound x C.radius_pos w hw hw0
  refine ⟨c,w,B,hB,hc,hcp,hw,fun η hη => ⟨hw0 η hη,rfl⟩,?_,hbound⟩
  intro q hq
  dsimp only [w]
  have hn := ne_of_gt (hcp q.1 hq.1)
  calc
    _ = c q.1 * (C.forwardDensity q / c q.1) := (mul_div_cancel₀ _ hn).symm
    _ = _ := by ring
end CanonicalFrameChartData
end RothschildStein.L1
