-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.Definitions.basePoint
public import RothschildStein.Definitions.joinPoint
public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.PiProd

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
namespace RothschildStein.P1

/-- Continuous projection to the original coordinates in the
specified product-padding construction. -/
def paddingBaseCLM (n d : ℕ) : (Fin (n + d) → ℝ) →L[ℝ] (Fin n → ℝ) :=
  ContinuousLinearMap.pi (fun j => ContinuousLinearMap.proj (Fin.castAdd d j))

/-- Continuous projection to the added diffusion coordinates. -/
def paddingFiberCLM (n d : ℕ) : (Fin (n + d) → ℝ) →L[ℝ] (Fin d → ℝ) :=
  ContinuousLinearMap.pi (fun j => ContinuousLinearMap.proj (Fin.natAdd n j))

/-- The continuous joining map uses `joinPoint`,
with the original coordinates first and the added coordinates last. -/
def paddingJoinCLM (n d : ℕ) :
    ((Fin n → ℝ) × (Fin d → ℝ)) →L[ℝ] (Fin (n + d) → ℝ) :=
  ContinuousLinearMap.pi (Fin.addCases
    (fun j => (ContinuousLinearMap.proj j).comp (ContinuousLinearMap.fst ℝ _ _))
    (fun j => (ContinuousLinearMap.proj j).comp (ContinuousLinearMap.snd ℝ _ _)))

/-- The base projection is exactly `basePoint`. -/
theorem paddingBaseCLM_apply (n d : ℕ) (ξ : Fin (n + d) → ℝ) :
    paddingBaseCLM n d ξ = basePoint ξ := rfl

/-- The continuous join is exactly `joinPoint`. -/
theorem paddingJoinCLM_apply (n d : ℕ) (x : Fin n → ℝ) (z : Fin d → ℝ) :
    paddingJoinCLM n d (x, z) = joinPoint x z := by
  ext j
  refine Fin.addCases ?_ ?_ j
  · intro i
    simp [paddingJoinCLM, joinPoint]
  · intro i
    simp [paddingJoinCLM, joinPoint]

end RothschildStein.P1
