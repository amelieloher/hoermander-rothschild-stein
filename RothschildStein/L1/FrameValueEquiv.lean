-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module
public import RothschildStein.L1.FrameCoefficientFields
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic
public import Mathlib.Analysis.Normed.Module.FiniteDimension
@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open scoped BigOperators
namespace RothschildStein.L1

/-- Independence of a square tangent frame makes its coefficient
map injective. -/
theorem frameValueCLM_injective {N : ℕ}
    (Y : Fin N → (Fin N → ℝ) → (Fin N → ℝ)) (x : Fin N → ℝ)
    (hY : LinearIndependent ℝ (fun i => Y i x)) :
    Function.Injective (frameValueCLM Y x) := by
  classical
  apply LinearMap.ker_eq_bot.mp
  apply LinearMap.ker_eq_bot'.mpr
  intro u hu
  have hz : ∑ i, u i • Y i x = 0 := by
    change frameValueCLM Y x u = 0 at hu
    simpa only [frameValueCLM_apply,frameCoefficientField] using hu
  ext i
  exact (linearIndependent_iff'.mp hY Finset.univ u (by simpa using hz)) i
    (Finset.mem_univ i)

/-- The invertible coefficient map of a tangent frame. -/
def frameValueEquiv {N : ℕ}
    (Y : Fin N → (Fin N → ℝ) → (Fin N → ℝ)) (x : Fin N → ℝ)
    (hY : LinearIndependent ℝ (fun i => Y i x)) :
    (Fin N → ℝ) ≃L[ℝ] (Fin N → ℝ) :=
  (LinearEquiv.ofInjectiveEndo (frameValueCLM Y x).toLinearMap
    (frameValueCLM_injective Y x hY)).toContinuousLinearEquiv

/-- The frame equivalence has exactly the actual coefficient map. -/
theorem frameValueEquiv_apply {N : ℕ}
    (Y : Fin N → (Fin N → ℝ) → (Fin N → ℝ)) (x : Fin N → ℝ)
    (hY : LinearIndependent ℝ (fun i => Y i x)) (u : Fin N → ℝ) :
    frameValueEquiv Y x hY u = frameValueCLM Y x u := rfl
end RothschildStein.L1
