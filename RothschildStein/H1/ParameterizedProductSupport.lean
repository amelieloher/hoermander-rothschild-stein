-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import Mathlib.Topology.Algebra.Support
public import Mathlib.Topology.Constructions.SumProd
public import Mathlib.Basic.Real.Basic

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
open Set
namespace RothschildStein.H1

/-- A compact cutoff in the group parameter makes a
translated compact function compact on the joint carrier. -/
theorem hasCompactSupport_parameterizedProduct
    {E : Type*} [TopologicalSpace E] [T2Space E]
    {F I : E × E → E} (hI : Continuous I)
    (hInv : ∀ x w, I (F (x, w), w) = x)
    {ψ η : E → ℝ} (hψ : HasCompactSupport ψ) (hη : HasCompactSupport η) :
    HasCompactSupport (fun p : E × E => ψ (F p) * η p.2) := by
  let K := (fun p : E × E => (I p, p.2)) '' (tsupport ψ ×ˢ tsupport η)
  have hK : IsCompact K := (hψ.prod hη).image (hI.prodMk continuous_snd)
  apply HasCompactSupport.of_support_subset_isCompact hK
  intro p hp
  have hp' : ψ (F p) ≠ 0 ∧ η p.2 ≠ 0 := mul_ne_zero_iff.mp hp
  refine ⟨(F p, p.2), ⟨subset_closure hp'.1, subset_closure hp'.2⟩, ?_⟩
  apply Prod.ext
  · exact hInv p.1 p.2
  · rfl

end RothschildStein.H1
