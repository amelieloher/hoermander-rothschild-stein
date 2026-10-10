-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Semigroup.FormResolvent

/-! # The operator graph defined by an injective resolvent

The pairs `(R f, f - R f)` define the inverse-resolvent operator. Its domain and adjoint
graph can be identified directly, without an unbounded spectral theorem.
-/

@[expose] public section
noncomputable section
open Set

namespace HeatKernel
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- The graph relation of the operator whose resolvent at one is `R`. -/
def InverseResolventGraph (R : H →L[ℝ] H) (u g : H) : Prop :=
  ∃ f, u = R f ∧ g = f - R f

theorem inverseResolventGraph_iff (R : H →L[ℝ] H) (u g : H) :
    InverseResolventGraph R u g ↔ R (u + g) = u := by
  constructor
  · rintro ⟨f, rfl, rfl⟩
    simp
  · intro h
    refine ⟨u + g, h.symm, ?_⟩
    rw [h]
    abel

variable [CompleteSpace H]

theorem inverseResolventGraph_adjoint_iff (R : H →L[ℝ] H) (hR : IsSelfAdjoint R)
    (y g : H) :
    (∀ f, inner ℝ (f - R f) y = inner ℝ (R f) g) ↔ InverseResolventGraph R y g := by
  rw [inverseResolventGraph_iff]
  have hsym (a b : H) : inner ℝ (R a) b = inner ℝ a (R b) := hR.isSymmetric a b
  constructor
  · intro h
    apply ext_inner_left ℝ
    intro f
    rw [map_add, inner_add_right, ← hsym f y, ← hsym f g]
    have he := h f
    rw [inner_sub_left] at he
    linarith
  · intro h f
    have he := congrArg (fun z => inner ℝ f z) h
    rw [map_add, inner_add_right, ← hsym f y, ← hsym f g] at he
    rw [inner_sub_left]
    linarith

theorem inverseResolventGraph_symm (R : H →L[ℝ] H) (hR : IsSelfAdjoint R)
    {u g v h : H} (hu : InverseResolventGraph R u g)
    (hv : InverseResolventGraph R v h) : inner ℝ g v = inner ℝ u h := by
  obtain ⟨f, rfl, rfl⟩ := hu
  exact (inverseResolventGraph_adjoint_iff R hR v h).mpr hv f

end HeatKernel
