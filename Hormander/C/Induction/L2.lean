-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import Hormander.C.Induction.Words

@[expose] public section

noncomputable section

open MeasureTheory SchwartzMap
open scoped ComplexConjugate ComplexInnerProductSpace
namespace Hormander.C
open Hormander.B
variable {N : ℕ}

local instance : Fact (1 ≤ (2 : ENNReal)) := ⟨by norm_num⟩

theorem hermitianPairing_eq_inner (u v : TestFunction N) :
    hermitianPairing u v = inner ℂ (v.toLp 2) (u.toLp 2) := by
  rw [MeasureTheory.L2.inner_def]
  unfold hermitianPairing
  refine integral_congr_ae ?_
  filter_upwards [SchwartzMap.coeFn_toLp v 2 volume, SchwartzMap.coeFn_toLp u 2 volume] with x hv hu
  rw [hv, hu]
  simp

theorem norm_H_le (u v : TestFunction N) :
    ‖hermitianPairing u v‖ ≤ sobolevNorm 0 u * sobolevNorm 0 v := by
  rw [hermitianPairing_eq_inner, sobolevNorm_zero_order, sobolevNorm_zero_order, mul_comm]
  exact norm_inner_le_norm _ _

theorem sobolevNorm_zero_sq (u : TestFunction N) : sobolevNorm 0 u ^ 2 = normSq u := by
  have h := H_self u
  rw [hermitianPairing_eq_inner, inner_self_eq_norm_sq_to_K] at h
  rw [sobolevNorm_zero_order]
  apply Complex.ofReal_injective
  push_cast
  exact h

end Hormander.C
