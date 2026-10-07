-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H3.GroupSetting

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
namespace RothschildStein.H3
open Set Metric MeasureTheory
open scoped ENNReal
variable {N : ℕ} (G : HomogeneousGroup N)

/-- The radius-three ball has positive finite measure. -/
def groupVolumeLower (ν : G2.HomogeneousNorm G) : ℝ :=
  (volume (G2.gaugeBall G ν (0 : Fin N → ℝ) 3)).toReal

/-- Exact homogeneous ball volume provides the uniform lower mass;
no centre-dependent constant is needed (BB pp. 357–359). -/
theorem groupVolumeLower_spec (ν : G2.HomogeneousNorm G)
    (h1 : ν.c = 1) (hsym : ν.Symmetric) :
    letI := gaugeMetric G ν h1 hsym
    0 < groupVolumeLower G ν ∧
      ∀ z ∈ (groupSetting G ν h1 hsym).Ω₁,
        ENNReal.ofReal (groupVolumeLower G ν) ≤
          (groupSetting G ν h1 hsym).μ
            (ball z (groupSetting G ν h1 hsym).κ) := by
  let := gaugeMetric G ν h1 hsym
  have hpos := G2.volume_gaugeBall_pos G ν.gauge (0 : Fin N → ℝ) (by norm_num : 0 < (3 : ℝ))
  have hfin := G2.volume_gaugeBall_ne_top G ν.gauge (0 : Fin N → ℝ) 3
  constructor
  · exact ENNReal.toReal_pos hpos.ne' hfin
  · intro z _
    change ENNReal.ofReal (volume (G2.gaugeBall G ν (0 : Fin N → ℝ) 3)).toReal ≤
      volume (G2.gaugeBall G ν z 3)
    rw [ENNReal.ofReal_toReal hfin]
    have hvol (x : Fin N → ℝ) :
        volume (G2.gaugeBall G ν x 3) = volume (G2.gaugeBall G ν 0 3) := by
      rw [G2.volume_gaugeBall ν.gauge x (by norm_num : 0 < (3 : ℝ)),
        G2.volume_gaugeBall ν.gauge 0 (by norm_num : 0 < (3 : ℝ))]
    exact (hvol z).symm.le

end RothschildStein.H3
