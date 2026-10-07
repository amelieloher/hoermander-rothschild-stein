-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H1.DyadicPairingLimit
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Mathlib.Topology.MetricSpace.Pseudo.Basic

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
open Set MeasureTheory Filter Topology
namespace RothschildStein.H1
variable {N : ℕ}

/-- Step 5: uniform limits of continuous functions commute
with pairing against every compact continuous test. -/
theorem tendsto_integral_mul_compact_of_uniformLimit
    {ι : Type*} {l : Filter ι} [l.IsCountablyGenerated]
    {F : ι → (Fin N → ℝ) → ℝ} {f φ : (Fin N → ℝ) → ℝ}
    (hF : ∀ i, Continuous (F i)) (hf : Continuous f)
    (hφ : Continuous φ) (hsφ : HasCompactSupport φ) (ht : TendstoUniformly F f l) :
    Tendsto (fun i => ∫ x, F i x * φ x) l (𝓝 (∫ x, f x * φ x)) := by
  let D := fun x => (‖f x‖ + 1) * ‖φ x‖
  have hcD : Continuous D := (hf.norm.add continuous_const).mul hφ.norm
  have hsD : HasCompactSupport D := hsφ.norm.mul_left
  have hiD : Integrable D volume := hcD.integrable_of_hasCompactSupport hsD
  apply tendsto_integral_filter_of_dominated_convergence D
  · exact Eventually.of_forall fun i => ((hF i).mul hφ).aestronglyMeasurable
  · have he := (Metric.tendstoUniformly_iff.mp ht) 1 (by norm_num)
    filter_upwards [he] with i hi
    apply Eventually.of_forall
    intro x
    have hn : ‖F i x - f x‖ < 1 := by
      simpa only [dist_comm, dist_eq_norm] using hi x
    have hb : ‖F i x‖ ≤ ‖f x‖ + 1 := by
      calc
        _ ≤ ‖F i x - f x‖ + ‖f x‖ := norm_le_norm_sub_add _ _
        _ ≤ _ := by linarith
    change ‖F i x * φ x‖ ≤ (‖f x‖ + 1) * ‖φ x‖
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_right hb (norm_nonneg _)
  · exact hiD
  · exact Eventually.of_forall fun x => (ht.tendsto_at x).mul tendsto_const_nhds

end RothschildStein.H1
