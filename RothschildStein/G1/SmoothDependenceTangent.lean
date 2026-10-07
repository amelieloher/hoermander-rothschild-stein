-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.G1.SmoothDependenceError
public import Mathlib.Analysis.Calculus.FDeriv.Partial

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set Filter
open scoped Topology ContDiff

namespace RothschildStein.G1

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The nonlinear field together with its first variational equation. -/
def tangentVectorField (Z : E → E) (p : E × (E →L[ℝ] E)) : E × (E →L[ℝ] E) :=
  (Z p.1, (fderiv ℝ Z p.1).comp p.2)

/-- Passing to the variational field loses one derivative.
This is the field used in the induction on regularity
(BB Proposition 1.2, p. 3). -/
theorem tangentVectorField_contDiffOn
    {Ω : Set E} (hΩ : IsOpen Ω) {Z : E → E} {n m : ℕ∞ω}
    (hZ : ContDiffOn ℝ m Z Ω) (hn : n + 1 ≤ m) :
    ContDiffOn ℝ n (tangentVectorField Z) (Ω ×ˢ univ) := by
  have hbase : ContDiffOn ℝ n (fun p : E × (E →L[ℝ] E) => Z p.1) (Ω ×ˢ univ) := (hZ.of_le (le_trans (le_self_add) hn)).comp
    contDiffOn_fst (prod_subset_preimage_fst _ _)
  have hdf : ContDiffOn ℝ n (fun p : E × (E →L[ℝ] E) => fderiv ℝ Z p.1)
      (Ω ×ˢ univ) := (hZ.fderiv_of_isOpen hΩ hn).comp
    contDiffOn_fst (prod_subset_preimage_fst _ _)
  exact hbase.prodMk (hdf.clm_comp contDiffOn_snd)

end RothschildStein.G1
