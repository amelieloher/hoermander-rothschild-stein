-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H3.CompactQuasiballCutoff
public import RothschildStein.G2.SobolevCutoff
public import RothschildStein.G2.Algebra

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public section
noncomputable section
open MeasureTheory Filter
open scoped Topology ENNReal
namespace RothschildStein.H3

/-- The actual concentric smooth cutoff is the anisotropic dilation of
one fixed unit cutoff. -/
theorem expandingCutoff_eq_groupSobolevCutoff {N : ℕ}
    (G : HomogeneousGroup N) (ν : G2.HomogeneousNorm G)
    {R : ℝ} (hR : 0 < R) :
    smoothQuasiballCutoff G ν 0 R (2*R) =
      G2.groupSobolevCutoff G (smoothQuasiballCutoff G ν 0 1 2) R := by
  funext x
  simp only [smoothQuasiballCutoff, G2.groupSobolevCutoff,
    G2.inv_zero, G2.zero_mul]
  rw [ν.gauge.2.2.2 R⁻¹ (inv_pos.mpr hR) x]
  unfold quasiballProfile
  congr 1
  field_simp

/-- Expanding smooth gauge cutoffs converge to the identity on every
finite positive Lp space. This uses the proved G2 cutoff convergence. -/
theorem tendsto_expandingCutoff_mul_eLpNorm {N : ℕ}
    (G : HomogeneousGroup N) (ν : G2.HomogeneousNorm G) (hν : ν.Smooth)
    {p : ℝ} (hp : 0 < p) {f : (Fin N → ℝ) → ℝ}
    (hf : MemLp f (ENNReal.ofReal p) volume) :
    Tendsto (fun R : ℝ => eLpNorm
      (fun x => f x * smoothQuasiballCutoff G ν 0 R (2*R) x - f x)
      (ENNReal.ofReal p) volume) atTop (𝓝 0) := by
  have hc := smoothQuasiballCutoff_contDiff G ν hν 0
    (by norm_num : (0 : ℝ) < 1) (by norm_num : (1 : ℝ) < 2)
  have ht := G2.tendsto_groupSobolevCutoff_mul_eLpNorm G ν hc.continuous
    (fun x => smoothQuasiballCutoff_range G ν 0 x 1 2)
    (fun x hx => by
      simp only [smoothQuasiballCutoff, G2.inv_zero, G2.zero_mul]
      exact quasiballProfile_one (by norm_num) hx) hp hf
  apply ht.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with R hR
  rw [expandingCutoff_eq_groupSobolevCutoff G ν hR]

end RothschildStein.H3
