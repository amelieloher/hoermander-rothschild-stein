-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.S.DistanceMetricLaws

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
open Set TopologicalSpace
open scoped ENNReal
namespace RothschildStein.S
variable {n : ℕ} {Ω : Opens (Fin n → ℝ)}

/-- Euclidean closure of a distance ball is contained in the
closed distance ball whenever its closure remains in the ambient domain.
The distance remains the original ambient one (BB p. 85). -/
theorem DistanceGeometry.ambient_closure_ball_subset
    (G : DistanceGeometry Ω) (x : Ω) (R : ℝ≥0∞)
    (hc : closure {y : Fin n → ℝ | y ∈ (Ω : Set (Fin n → ℝ)) ∧ G.d x.val y < R} ⊆ Ω) :
    closure {y : Fin n → ℝ | y ∈ (Ω : Set (Fin n → ℝ)) ∧ G.d x.val y < R} ⊆
      {y : Fin n → ℝ | y ∈ (Ω : Set (Fin n → ℝ)) ∧ G.d x.val y ≤ R} := by
  intro y hy
  refine ⟨hc hy,?_⟩
  have hm : MapsTo (G.d x.val)
      {y : Fin n → ℝ | y ∈ (Ω : Set (Fin n → ℝ)) ∧ G.d x.val y < R} (Iic R) :=
    fun _ hz => hz.2.le
  have ht := hm.closure_of_continuousOn ((G.continuousOn_distance x).mono hc) hy
  simpa only [closure_Iic,mem_Iic] using ht

end RothschildStein.S
