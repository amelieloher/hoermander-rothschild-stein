-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.G1.ComparisonControlTopology
public import Mathlib.Analysis.SpecificLimits.Basic

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set Filter
open scoped Topology ENNReal
namespace RothschildStein.G4
open G1

/-- Geometric actual-control costs pass to the Euclidean
endpoint under the local comparison of Euclidean and control topologies. This uses the extended
metric directly and does not require global distance finiteness or an
infinite concatenated controlled curve (BB pp. 459–460). -/
theorem controlDistance_geometric_correction_of_local_comparison {m n s : ℕ}
    {Ω : Set (Fin n → ℝ)} (hΩ : IsOpen Ω) (w : Fin m → ℕ+)
    (X : Fin m → (Fin n → ℝ) → (Fin n → ℝ))
    (hX : ∀ i, ContinuousOn (X i) Ω) (hs : 0 < s)
    (hcomparison : LocalControlComparison Ω w X s)
    (z : ℕ → Ω) (y : Ω) (C : ℝ)
    (hcost : ∀ j, controlDistance Ω w X (z j).val (z (j + 1)).val ≤
      ENNReal.ofReal C / (2 : ℝ≥0∞) ^ j)
    (hlimit : Tendsto z atTop (𝓝 y)) :
    controlDistance Ω w X (z 0).val y.val ≤ ENNReal.ofReal (2 * C) := by
  have he := controlEMetricSpace_topology_eq_of_local_comparison hΩ w X hX hs hcomparison
  have ht : Tendsto z atTop
      (@nhds Ω (controlEMetricSpace hΩ w X hX).toUniformSpace.toTopologicalSpace y) := by
    rw [he]
    exact hlimit
  let controlSpace : EMetricSpace Ω := controlEMetricSpace hΩ w X hX
  have hh := @edist_le_of_edist_le_geometric_two_of_tendsto₀ Ω
    controlSpace.toPseudoEMetricSpace (ENNReal.ofReal C) z hcost y ht
  simpa only [controlSpace, controlEMetricSpace_edist, ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2),
    ENNReal.ofReal_ofNat] using hh

end RothschildStein.G4
