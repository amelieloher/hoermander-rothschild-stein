-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.G1.LocalFlows
public import RothschildStein.Definitions.hasIntrinsicDeriv

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public section
noncomputable section
open Set Filter Metric TopologicalSpace
open scoped Topology
namespace RothschildStein.S
variable {n : ℕ}

/-- A locally smooth field has an integral curve through each point, as required by the intrinsic derivative definition (BB Proposition 1.2, p. 3). -/
theorem exists_intrinsic_integral_curve
    (Ω : Opens (Fin n → ℝ)) (X : (Fin n → ℝ) → (Fin n → ℝ))
    (hX : ContDiffOn ℝ (⊤ : ℕ∞) X (Ω : Set (Fin n → ℝ)))
    {x : Fin n → ℝ} (hx : x ∈ (Ω : Set (Fin n → ℝ))) :
    ∃ γ : ℝ → (Fin n → ℝ),γ 0 = x ∧
      IsIntegralCurveAt γ (fun _ => X) 0 ∧
      ∀ᶠ t in 𝓝 (0 : ℝ),γ t ∈ (Ω : Set (Fin n → ℝ)) := by
  obtain ⟨r,hr,τ,hτ,Φ,hball,hct,hΦ⟩ :=
    RothschildStein.G1.exists_continuous_local_flow Ω.isOpen X hX hx
  have H := hΦ x (mem_ball_self hr)
  refine ⟨fun t => Φ (x,t),H.1,?_,?_⟩
  · filter_upwards [Ioo_mem_nhds (by linarith : -τ < (0 : ℝ)) hτ] with t ht
    exact (H.2 t ht).2
  · filter_upwards [Ioo_mem_nhds (by linarith : -τ < (0 : ℝ)) hτ] with t ht
    exact (H.2 t ht).1

end RothschildStein.S
