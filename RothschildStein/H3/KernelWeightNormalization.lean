-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H3.GroupSetting
public import RothschildStein.H2.KernelClass
public import RothschildStein.H3.TruncatedKernelSize

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public section
noncomputable section
open Set Metric MeasureTheory
namespace RothschildStein.H3
variable {N : ℕ} (G : HomogeneousGroup N)

/-- The H2 ball-volume weight on the group has its exact
normalization by the volume of the unit gauge ball. -/
theorem kernelWeight_gauge_eq (ν : G2.HomogeneousNorm G)
    (h1 : ν.c = 1) (hsym : ν.Symmetric) (v : ℝ) :
    letI := gaugeMetric G ν h1 hsym
    ∀ x y : ControlCarrier N, x ≠ y →
      H2.kernelWeight volume v x y =
        G2.gaugeDistance G ν x y ^ (v - (G.homogeneousDimension : ℝ)) /
          (volume {z : Fin N → ℝ | ν z < 1}).toReal := by
  let : MetricSpace (ControlCarrier N) := gaugeMetric G ν h1 hsym
  intro x y hxy
  have hd : 0 < dist x y := dist_pos.mpr hxy
  have hv := G2.volume_gaugeBall ν.gauge x hd
  have hvb : H2.volumeAt (volume : Measure (ControlCarrier N)) x y =
      ENNReal.ofReal (dist x y ^ G.homogeneousDimension) *
        volume {z : Fin N → ℝ | ν z < 1} := hv
  have hrvol : (H2.volumeAt (volume : Measure (ControlCarrier N)) x y).toReal =
      dist x y ^ G.homogeneousDimension *
        (volume {z : Fin N → ℝ | ν z < 1}).toReal := by
    simpa only [ENNReal.toReal_mul, ENNReal.toReal_ofReal (pow_nonneg hd.le G.homogeneousDimension)] using
      congrArg ENNReal.toReal hvb
  change dist x y ^ v / (H2.volumeAt volume x y).toReal =
    dist x y ^ (v - (G.homogeneousDimension : ℝ)) /
      (volume {z : Fin N → ℝ | ν z < 1}).toReal
  rw [hrvol, div_mul_eq_div_div, ← Real.rpow_natCast, ← Real.rpow_sub hd]

/-- Unit gauge-ball volume is strictly positive and finite,
so converting the homogeneous size estimate to H2 loses no information. -/
theorem gauge_unit_volume_toReal_pos (ν : G2.HomogeneousNorm G) :
    0 < (volume {z : Fin N → ℝ | ν z < 1}).toReal := by
  have he := G2.volume_gaugeBall ν.gauge (0 : Fin N → ℝ) (by norm_num : (0 : ℝ) < 1)
  simp only [one_pow, ENNReal.ofReal_one, one_mul] at he
  rw [← he]
  exact ENNReal.toReal_pos
    (G2.volume_gaugeBall_pos G ν.gauge 0 (by norm_num)).ne'
    (G2.volume_gaugeBall_ne_top G ν.gauge 0 1)

/-- size in the shared kernel hypotheses. The constant contains unit-ball
volume m rather than its reciprocal (BB p. 350). -/
theorem truncatedKernel_h2_size (ν : G2.HomogeneousNorm G)
    (h1 : ν.c = 1) (hsym : ν.Symmetric)
    {T χ : (Fin N → ℝ) → ℝ} (hT : ContinuousOn T {0}ᶜ) {α v : ℝ}
    (hhom : ∀ t : ℝ, 0 < t → ∀ x, x ≠ 0 →
      T (G.dilate t x) = t ^ (α - (G.homogeneousDimension : ℝ)) * T x)
    (hv : v ≤ α) {R : ℝ} (hR : 0 < R)
    (hχ : ∀ x, 0 ≤ χ x ∧ χ x ≤ 1)
    (hsupp : ∀ x, R < ν x → χ x = 0) :
    letI := gaugeMetric G ν h1 hsym
    ∀ x y : ControlCarrier N, x ≠ y →
      |χ (G.mul (G.inv y) x) * T (G.mul (G.inv y) x)| ≤
        ((volume {z : Fin N → ℝ | ν z < 1}).toReal *
          kernelSphereBound ν T * R ^ (α - v)) * H2.kernelWeight volume v x y := by
  let : MetricSpace (ControlCarrier N) := gaugeMetric G ν h1 hsym
  intro x y hxy
  have hz : G.mul (G.inv y) x ≠ 0 := by
    intro hz
    have hd : dist x y = 0 := by
      change ν (G.mul (G.inv y) x) = 0
      rw [hz, (ν.gauge.2.2.1 0).mpr rfl]
    exact hxy (dist_eq_zero.mp hd)
  have hb := truncatedHomogeneousKernel_size ν.gauge hT hhom hv hR hχ hsupp
    (G.mul (G.inv y) x) hz
  rw [kernelWeight_gauge_eq G ν h1 hsym v x y hxy]
  have hm := gauge_unit_volume_toReal_pos G ν
  have he : ((volume {z : Fin N → ℝ | ν z < 1}).toReal *
      kernelSphereBound ν T * R ^ (α - v)) *
      (G2.gaugeDistance G ν x y ^ (v - (G.homogeneousDimension : ℝ)) /
        (volume {z : Fin N → ℝ | ν z < 1}).toReal) =
      kernelSphereBound ν T * R ^ (α - v) *
        ν (G.mul (G.inv y) x) ^ (v - (G.homogeneousDimension : ℝ)) := by
    unfold G2.gaugeDistance
    field_simp [hm.ne']
  rw [he]
  exact hb

end RothschildStein.H3
