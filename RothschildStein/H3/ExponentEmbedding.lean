-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H2.HolderModule

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
namespace RothschildStein.H3
open Set Metric MeasureTheory
open scoped NNReal ENNReal
variable {X : Type*} [MetricSpace X]

/-- On a bounded ball, higher Holder exponents embed into lower
ones. This supplies a common dense domain for the fixed-exponent L2
extensions (BB pp. 357–359, uniqueness argument). -/
theorem boundedHolder_exponent_mono_ball {δ s : ℝ≥0} {o : X} {R : ℝ}
    (hR : 0 < R) (hδs : δ ≤ s) {f : X → ℝ}
    (hf : H2.BoundedHolder s (ball o R) f) : H2.BoundedHolder δ (ball o R) f := by
  have hm : MemHolder s (fun x : ball o R => f x) :=
    eHolderNorm_lt_top.mp hf.parts.2
  have hd : ∀ x y : ball o R, edist x y ≤ (Real.toNNReal (2 * R) : ℝ≥0∞) := by
    intro x y
    have hxy : dist (x : X) (y : X) ≤ 2 * R := by
      have hx : dist (x : X) o < R := x.property
      have hy' : dist (y : X) o < R := y.property
      have hy : dist o (y : X) < R := by simpa only [dist_comm] using hy'
      exact (dist_triangle (x : X) o (y : X)).trans (by linarith)
    rw [edist_dist]
    change ENNReal.ofReal (dist (x : X) (y : X)) ≤ (Real.toNNReal (2 * R) : ℝ≥0∞)
    rw [← ENNReal.ofReal_coe_nnreal]
    apply ENNReal.ofReal_le_ofReal
    simpa only [Real.coe_toNNReal', max_eq_left (by positivity : 0 ≤ 2 * R)] using hxy
  have hn := (HolderWith.of_le hd hm.holderWith hδs).memHolder.eHolderNorm_lt_top
  exact ENNReal.add_lt_top.mpr ⟨hf.parts.1, hn⟩

end RothschildStein.H3
