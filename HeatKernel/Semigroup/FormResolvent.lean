-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import Mathlib.Analysis.InnerProductSpace.Positive
public import Mathlib.Topology.DenseEmbedding

/-! # Resolvents from a Hilbert form inclusion

For a complete form space, the adjoint of its continuous inclusion is the Riesz solution
operator. Composing with the inclusion gives the bounded resolvent on the ambient space.
-/

@[expose] public section
noncomputable section
open Set
open scoped InnerProduct

namespace HeatKernel
variable {V H : Type*}
    [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- The bounded resolvent associated with the inclusion of a Hilbert form domain. -/
def formResolvent (j : V →L[ℝ] H) : H →L[ℝ] H := j.comp j.adjoint

theorem inner_adjoint_formInclusion (j : V →L[ℝ] H) (f : H) (v : V) :
    inner ℝ (j.adjoint f) v = inner ℝ f (j v) := j.adjoint_inner_left v f

theorem formResolvent_isPositive (j : V →L[ℝ] H) :
    (formResolvent j).IsPositive := j.isPositive_self_comp_adjoint

theorem formResolvent_isSelfAdjoint (j : V →L[ℝ] H) :
    IsSelfAdjoint (formResolvent j) := (formResolvent_isPositive j).isSelfAdjoint

theorem norm_formResolvent_le_one (j : V →L[ℝ] H) (hj : ‖j‖ ≤ 1) :
    ‖formResolvent j‖ ≤ 1 := by
  calc
    ‖formResolvent j‖ ≤ ‖j‖ * ‖j.adjoint‖ := ContinuousLinearMap.opNorm_comp_le _ _
    _ = ‖j‖ * ‖j‖ := by rw [ContinuousLinearMap.adjoint.norm_map]
    _ ≤ 1 := by nlinarith [norm_nonneg j]

theorem formResolvent_injective_of_denseRange (j : V →L[ℝ] H) (hdense : DenseRange j) :
    Function.Injective (formResolvent j) := by
  have hker : j.adjoint.ker = ⊥ := by
    rw [← j.orthogonal_range, ← Submodule.topologicalClosure_eq_top_iff,
      ← Submodule.dense_iff_topologicalClosure_eq_top]
    exact hdense
  have hi : Function.Injective j.adjoint := LinearMap.ker_eq_bot.mp hker
  exact j.self_comp_adjoint_injective_iff.mpr hi

/-- The energy identity identifies the form operator without choosing an inverse. -/
theorem formEquation_iff_resolvent_eq_of_injective (j : V →L[ℝ] H)
    (hj : Function.Injective j) (u : V) (g : H) :
    (∀ v, inner ℝ u v - inner ℝ (j u) (j v) = inner ℝ g (j v)) ↔
      formResolvent j (j u + g) = j u := by
  constructor
  · intro h
    have hu : j.adjoint (j u + g) = u := by
      apply ext_inner_right ℝ
      intro v
      rw [inner_adjoint_formInclusion, inner_add_left]
      linarith [h v]
    change j (j.adjoint (j u + g)) = j u
    rw [hu]
  · intro h v
    have hu : j.adjoint (j u + g) = u := hj h
    have he := inner_adjoint_formInclusion j (j u + g) v
    rw [hu, inner_add_left] at he
    linarith

end HeatKernel
