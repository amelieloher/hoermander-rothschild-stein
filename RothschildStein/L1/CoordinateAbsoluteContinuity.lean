-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.L1.ScalarIntegration
public import Mathlib.Topology.MetricSpace.Pseudo.Pi

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set Filter
open scoped BigOperators

namespace RothschildStein.L1

/-- Finitely many absolutely continuous coordinates form an
absolutely continuous curve for the sup-norm coordinate carrier. -/
theorem absolutelyContinuousOnInterval_of_coordinates {m : ℕ} {a b : ℝ}
    (v : ℝ → (Fin m → ℝ))
    (hv : ∀ j, AbsolutelyContinuousOnInterval (fun t => v t j) a b) :
    AbsolutelyContinuousOnInterval v a b := by
  let f := AbsolutelyContinuousOnInterval.totalLengthFilter ⊓
    Filter.principal (AbsolutelyContinuousOnInterval.disjWithin a b)
  have hsum : Tendsto
      (fun E : ℕ × (ℕ → ℝ × ℝ) => ∑ j : Fin m,
        ∑ i ∈ Finset.range E.1, dist (v (E.2 i).1 j) (v (E.2 i).2 j)) f (nhds 0) := by
    simpa only [Finset.sum_const_zero] using
      (tendsto_finsetSum Finset.univ (fun j _ => hv j))
  apply squeeze_zero (fun _ => Finset.sum_nonneg (fun _ _ => dist_nonneg)) ?_ hsum
  intro E
  rw [Finset.sum_comm]
  apply Finset.sum_le_sum
  intro i _
  apply (dist_pi_le_iff (Finset.sum_nonneg (fun _ _ => dist_nonneg))).mpr
  intro j
  exact Finset.single_le_sum (fun _ _ => dist_nonneg) (Finset.mem_univ j)

end RothschildStein.L1
