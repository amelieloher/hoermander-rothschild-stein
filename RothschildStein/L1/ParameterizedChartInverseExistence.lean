-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.L1.ParameterizedChartInverse

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set

namespace RothschildStein.L1

/-- Fiberwise chart coverage constructs the actual joint smooth
inverse. Its values are selected before deriving smoothness by uniqueness;
no smooth inverse is an input (BB pp. 520–521). -/
theorem exists_smooth_parameterized_chart_inverse {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    {U V : Set (E × F)} (hU : IsOpen U) (hV : IsOpen V)
    (Ψ : E × F → E) (hΨ : ContDiffOn ℝ (⊤ : ℕ∞) Ψ U)
    (hinj : ∀ v, InjOn (fun u => Ψ (u, v)) {u | (u, v) ∈ U})
    (hcover : ∀ p ∈ V, ∃ u, (u, p.2) ∈ U ∧ Ψ (u, p.2) = p.1)
    (hderiv : ∀ p ∈ U, ∃ H : E ≃L[ℝ] E,
      (fderiv ℝ Ψ p).comp (ContinuousLinearMap.inl ℝ E F) = (H : E →L[ℝ] E)) :
    ∃ θ : E × F → E, ContDiffOn ℝ (⊤ : ℕ∞) θ V ∧
      (∀ p ∈ V, (θ p, p.2) ∈ U) ∧ (∀ p ∈ V, Ψ (θ p, p.2) = p.1) := by
  classical
  have hall : ∀ p : E × F, ∃ u : E, p ∈ V → (u, p.2) ∈ U ∧ Ψ (u, p.2) = p.1 := by
    intro p
    by_cases hp : p ∈ V
    · obtain ⟨u, hu, he⟩ := hcover p hp
      exact ⟨u, fun _ => ⟨hu, he⟩⟩
    · exact ⟨0, fun h => (hp h).elim⟩
  choose θ hθ using hall
  have hm : ∀ p ∈ V, (θ p, p.2) ∈ U := fun p hp => (hθ p hp).1
  have he : ∀ p ∈ V, Ψ (θ p, p.2) = p.1 := fun p hp => (hθ p hp).2
  exact ⟨θ, contDiffOn_parameterized_chart_inverse hU hV Ψ θ hΨ hinj hm he hderiv, hm, he⟩

end RothschildStein.L1
