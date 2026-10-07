-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import Mathlib.Analysis.Calculus.FDeriv.Prod
public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.PiProd

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set Filter
open scoped Topology
namespace RothschildStein.L1

/-- Holding the vertical parameter fixed gives precisely the
horizontal block of the full chart derivative (BB pp. 520–521). -/
theorem fderiv_horizontal_slice {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (Φ : E × F → E × F) (u : E) (v : F)
    (hΦ : DifferentiableAt ℝ Φ (u,v)) :
    ((ContinuousLinearMap.fst ℝ E F).comp (fderiv ℝ Φ (u,v))).comp
      (ContinuousLinearMap.inl ℝ E F) = fderiv ℝ (fun y => (Φ (y,v)).1) u := by
  have hi : HasFDerivAt (fun y : E => (y,v)) (ContinuousLinearMap.inl ℝ E F) u :=
    (hasFDerivAt_id u).prodMk (hasFDerivAt_const v u)
  exact (hΦ.hasFDerivAt.comp u hi).fst.fderiv.symm

/-- Projection equality on the actual open mixed box identifies
its horizontal derivative with the original shifted chart derivative;
a vertical block is not substituted for the full Jacobian. -/
theorem horizontal_derivative_eq_of_projection {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {U : Set E} {V : Set F} (hU : IsOpen U)
    (Φ : E × F → E × F) (Ψ : E → F → E)
    (hproj : ∀ y ∈ U, ∀ z ∈ V, (Φ (y,z)).1 = Ψ y z)
    {u : E} {v : F} (hu : u ∈ U) (hv : v ∈ V)
    (hΦ : DifferentiableAt ℝ Φ (u,v)) :
    ((ContinuousLinearMap.fst ℝ E F).comp (fderiv ℝ Φ (u,v))).comp
      (ContinuousLinearMap.inl ℝ E F) = fderiv ℝ (fun y => Ψ y v) u := by
  rw [fderiv_horizontal_slice Φ u v hΦ]
  have hmem : ∀ᶠ y in 𝓝 u, y ∈ U := hU.mem_nhds hu
  have he : (fun y => (Φ (y,v)).1) =ᶠ[𝓝 u] (fun y => Ψ y v) :=
    hmem.mono (fun y hy => hproj y hy v hv)
  exact he.fderiv_eq

end RothschildStein.L1
