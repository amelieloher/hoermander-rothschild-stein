-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import Mathlib.Analysis.ODE.ExistUnique

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set Metric Function ODE
open scoped NNReal

namespace RothschildStein.G4

/-- The continuous Picard flow retains the closed spatial buffer
from its fixed-point construction. This supplies the domain containment
needed for uniform time-one existence and smooth dependence on parameters. -/
theorem exists_picard_flow_with_buffer {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E]
    {f : ℝ → E → E} {tmin tmax : ℝ} {t₀ : Icc tmin tmax} {x₀ : E}
    {a r L K : ℝ≥0} (hf : IsPicardLindelof f t₀ x₀ a r L K) :
    ∃ Φ : E × ℝ → E, ContinuousOn Φ (closedBall x₀ r ×ˢ Icc tmin tmax) ∧
      ∀ x ∈ closedBall x₀ r, Φ (x, t₀) = x ∧
      ∀ t ∈ Icc tmin tmax, Φ (x, t) ∈ closedBall x₀ a ∧
        HasDerivWithinAt (fun v => Φ (x, v)) (f t (Φ (x, t))) (Icc tmin tmax) t := by
  classical
  have hex (x : E) (hx : x ∈ closedBall x₀ r) := FunSpace.exists_isFixedPt_next hf hx
  choose α hα using hex
  let Φ : E × ℝ → E := fun pt => if hx : pt.1 ∈ closedBall x₀ r then
    (α pt.1 hx).compProj pt.2 else 0
  have hinit : ∀ x ∈ closedBall x₀ r, Φ (x, t₀) = x := by
    intro x hx
    simp only [Φ, dite_eq_left hx]
    rw [FunSpace.compProj_val, ← hα, FunSpace.next_apply₀]
  have hsol : ∀ x ∈ closedBall x₀ r, ∀ t ∈ Icc tmin tmax,
      HasDerivWithinAt (fun v => Φ (x, v)) (f t (Φ (x, t))) (Icc tmin tmax) t := by
    intro x hx t ht
    simp only [Φ, dite_eq_left hx]
    apply hasDerivWithinAt_picard_Icc t₀.property hf.continuousOn_uncurry
      (α x hx).continuous_compProj.continuousOn
      (fun _ _ => (α x hx).compProj_mem_closedBall hf.mul_max_le) x ht |>.congr_of_mem _ ht
    intro t' ht'
    nth_rw 1 [← hα]
    rw [FunSpace.compProj_of_mem ht', FunSpace.next_apply]
  obtain ⟨L', hbound⟩ := FunSpace.exists_forall_closedBall_funSpace_dist_le_mul hf
  have hLip : ∀ t ∈ Icc tmin tmax, LipschitzOnWith L' (fun x => Φ (x, t)) (closedBall x₀ r) := by
    intro t ht
    apply LipschitzOnWith.of_dist_le_mul
    intro x hx y hy
    simp only [Φ, dite_eq_left hx, dite_eq_left hy]
    rw [FunSpace.compProj_apply, FunSpace.compProj_apply,
      ← FunSpace.toContinuousMap_apply_eq_apply, ← FunSpace.toContinuousMap_apply_eq_apply]
    have : Nonempty (Icc tmin tmax) := ⟨t₀⟩
    apply ContinuousMap.dist_le_iff_of_nonempty.mp
    exact hbound x y hx hy (α x hx) (α y hy) (hα x hx) (hα y hy)
  have hc : ContinuousOn Φ (closedBall x₀ r ×ˢ Icc tmin tmax) :=
    continuousOn_prod_of_continuousOn_lipschitzOnWith _ L'
      (fun x hx => HasDerivWithinAt.continuousOn (hsol x hx)) hLip
  refine ⟨Φ, hc, ?_⟩
  intro x hx
  refine ⟨hinit x hx, ?_⟩
  intro t ht
  refine ⟨?_, hsol x hx t ht⟩
  simp only [Φ, dite_eq_left hx]
  exact (α x hx).compProj_mem_closedBall hf.mul_max_le

end RothschildStein.G4
