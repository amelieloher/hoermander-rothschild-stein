-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.S.FriedrichsKernelDefs
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.Topology.MetricSpace.Pseudo.Defs

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public section
noncomputable section
open Set MeasureTheory Function Metric Filter
open scoped Topology
namespace RothschildStein.S
variable {n : ℕ} {U : Set (Fin n → ℝ)} {δ : ℝ}

/-- The zeroth jet certificate supplies one size bound
uniform in x, displacement, and positive small scale (BB p. 76). -/
theorem BoundedFriedrichsKernel.exists_uniform_size (K : BoundedFriedrichsKernel U δ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ ε ∈ Ioo 0 δ, ∀ x ∈ U, ∀ y, ‖K.toFun ε x y‖ ≤ C := by
  obtain ⟨C,hC,hb⟩ := K.jetBound 0
  refine ⟨C,hC,?_⟩
  intro ε hε x hx y
  simpa only [norm_iteratedFDeriv_zero,uncurry] using! hb ε hε (x,y) ⟨hx,mem_univ y⟩

end RothschildStein.S
