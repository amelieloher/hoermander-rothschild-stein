-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.P1.TypeKernelSupport
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public section
noncomputable section
open Set Filter MeasureTheory
open scoped Topology
namespace RothschildStein.P1.TypeOperator
variable {N lam : ℕ} {F : KernelFrame N} [Nonempty (Fin N)]

/-- Every type operator, including type zero,
vanishes outside V; arbitrary diagonal values disappear almost everywhere. -/
theorem apply_eq_zero_outside (T : TypeOperator F lam) (f : (Fin N → ℝ) → ℝ)
    {ξ : Fin N → ℝ} (hξ : ξ ∉ (F.V : Set (Fin N → ℝ))) : T.apply f ξ = 0 := by
  have hrow : (fun η => T.kernel ξ η * f η) =ᵐ[volume] fun _ => 0 := by
    filter_upwards [volume.ae_ne ξ] with η hη
    rw [T.isType.eq_zero_of_outside hη.symm (Or.inl hξ), zero_mul]
  have hμ : T.mult ξ = 0 := image_eq_zero_of_notMem_tsupport
    (fun ht => hξ (T.mult.tsupport_subset ht))
  have htr (ε : ℝ) : T.truncated f ε ξ = 0 := by
    rw [truncated, integral_congr_ae (ae_restrict_of_ae hrow), integral_zero]
  by_cases he : lam = 0
  · rw [apply, ite_eq_left he, hμ, zero_mul, add_zero]
    simp_rw [htr]
    exact tendsto_const_nhds.limUnder_eq
  · rw [apply, ite_eq_right he, integral_congr_ae hrow, integral_zero]

end RothschildStein.P1.TypeOperator
