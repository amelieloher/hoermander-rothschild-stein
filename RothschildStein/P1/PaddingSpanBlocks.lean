-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.P1.PaddingLieWordEvaluation
public import Hormander.Interface.LieAlgebraSpansOn
public import Mathlib.Algebra.BigOperators.Pi

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public section
noncomputable section
open Set
open scoped BigOperators
namespace RothschildStein.P1

/-- A submodule containing every original direction and
all added coordinate diffusions is the whole padded carrier. -/
theorem submodule_eq_top_of_padding_directions {n d : ℕ}
    (M : Submodule ℝ (Fin (n + d) → ℝ))
    (hbase : ∀ v : Fin n → ℝ, joinPoint v (0 : Fin d → ℝ) ∈ M)
    (hadded : ∀ j : Fin d, paddingDiffusionField (n := n) j 0 ∈ M) :
    M = ⊤ := by
  classical
  let J : (Fin n → ℝ) →ₗ[ℝ] (Fin (n + d) → ℝ) :=
    ((paddingJoinCLM n d).comp (ContinuousLinearMap.inl ℝ _ _)).toLinearMap
  let K : (Fin d → ℝ) →ₗ[ℝ] (Fin (n + d) → ℝ) :=
    ((paddingJoinCLM n d).comp (ContinuousLinearMap.inr ℝ _ _)).toLinearMap
  have hJ (v : Fin n → ℝ) : J v = joinPoint v (0 : Fin d → ℝ) := by
    change paddingJoinCLM n d (v, 0) = _
    exact paddingJoinCLM_apply n d v 0
  have hK (v : Fin d → ℝ) : K v = joinPoint (0 : Fin n → ℝ) v := by
    change paddingJoinCLM n d (0, v) = _
    exact paddingJoinCLM_apply n d 0 v
  have hbase_mem (v : Fin n → ℝ) : J v ∈ M := by rw [hJ]; exact hbase v
  have hKb (j : Fin d) : K (Hormander.Interface.basisVec j) = paddingDiffusionField (n := n) j (0 : Fin (n + d) → ℝ) := by
    rw [hK]
    apply (paddingCoordinates n d).injective
    change (paddingBaseCLM n d (joinPoint 0 (Hormander.Interface.basisVec j)),
      paddingFiberCLM n d (joinPoint 0 (Hormander.Interface.basisVec j))) =
      (paddingBaseCLM n d (paddingDiffusionField (n := n) j (0 : Fin (n + d) → ℝ)),
        paddingFiberCLM n d (paddingDiffusionField (n := n) j (0 : Fin (n + d) → ℝ)))
    rw [paddingBaseCLM_join, paddingFiberCLM_join,
      paddingBaseCLM_diffusionField, paddingFiberCLM_diffusionField]
  have hfiber_mem (z : Fin d → ℝ) : K z ∈ M := by
    have hz : z = ∑ j, z j • Hormander.Interface.basisVec j := by
      simpa only [Hormander.Interface.basisVec] using pi_eq_sum_univ' z
    rw [hz, map_sum]
    apply M.sum_mem
    intro j hj
    rw [map_smul, hKb]
    exact M.smul_mem (z j) (hadded j)
  have hJK (v : Fin n → ℝ) (z : Fin d → ℝ) : J v + K z = paddingJoinCLM n d (v, z) := by
    change paddingJoinCLM n d (v, 0) + paddingJoinCLM n d (0, z) = _
    rw [← map_add]
    congr 1
    ext <;> simp
  change M = ⊤
  apply top_unique
  intro v hv
  have he : v = J (paddingBaseCLM n d v) + K (paddingFiberCLM n d v) :=
    (paddingJoinCLM_projections n d v).symm.trans (hJK _ _).symm
  rw [he]
  exact M.add_mem (hbase_mem _) (hfiber_mem _)

end RothschildStein.P1
