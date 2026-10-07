-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.G2.BallScaling

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
open Set MeasureTheory Filter
open scoped Topology
namespace RothschildStein.G2
variable {N : ℕ} {G : HomogeneousGroup N}

/-- Open and closed gauge balls have the same volume by translation and dilation invariance (BB Theorem 3.20, p. 105). -/
theorem volume_gaugeClosedBall_of_volumeScaling
    (htranslate : ∀ x : Fin N → ℝ, ∀ A : Set (Fin N → ℝ), volume ((G.mul x) '' A) = volume A)
    (hscale : ∀ r : ℝ, 0 < r → ∀ A : Set (Fin N → ℝ),
      volume ((G.dilate r) '' A) = ENNReal.ofReal (r ^ G.homogeneousDimension) * volume A)
    {ν : (Fin N → ℝ) → ℝ} (hν : G.IsHomogeneousGauge ν)
    (x : Fin N → ℝ) {r : ℝ} (hr : 0 < r) :
    volume (gaugeClosedBall G ν x r) = volume (gaugeBall G ν x r) := by
  apply le_antisymm
  · rw [volume_gaugeBall_of_volumeScaling htranslate hscale hν x hr]
    have hm : volume {u : Fin N → ℝ | ν u < 1} ≠ ⊤ :=
      ne_top_of_le_ne_top ((isCompact_gauge_le hν 1).measure_ne_top (μ := volume))
        (measure_mono fun u (hu : ν u < 1) => hu.le)
    have hc : Continuous (fun s : ℝ => ENNReal.ofReal (s ^ G.homogeneousDimension) *
        volume {u : Fin N → ℝ | ν u < 1}) :=
      (ENNReal.continuous_mul_const hm).comp
        (ENNReal.continuous_ofReal.comp (continuous_id.pow _))
    have ht : Tendsto (fun s : ℝ => ENNReal.ofReal (s ^ G.homogeneousDimension) *
        volume {u : Fin N → ℝ | ν u < 1}) (𝓝[>] r)
        (𝓝 (ENNReal.ofReal (r ^ G.homogeneousDimension) * volume {u : Fin N → ℝ | ν u < 1})) :=
      hc.continuousAt.tendsto.mono_left inf_le_left
    apply ge_of_tendsto ht
    filter_upwards [self_mem_nhdsWithin] with s hs
    have hrs : r < s := hs
    calc
      volume (gaugeClosedBall G ν x r) ≤ volume (gaugeBall G ν x s) := by
        apply measure_mono
        intro y hy
        change gaugeDistance G ν y x < s
        have hy' : gaugeDistance G ν y x ≤ r := hy
        exact hy'.trans_lt hrs
      _ = _ := volume_gaugeBall_of_volumeScaling htranslate hscale hν x (hr.trans hrs)
  · apply measure_mono
    intro y hy
    change gaugeDistance G ν y x ≤ r
    have hy' : gaugeDistance G ν y x < r := hy
    exact hy'.le

/-- Every positive-radius gauge sphere is null by translation and dilation invariance (BB Theorem 3.20, p. 105). -/
theorem volume_gaugeSphere_of_volumeScaling
    (htranslate : ∀ x : Fin N → ℝ, ∀ A : Set (Fin N → ℝ), volume ((G.mul x) '' A) = volume A)
    (hscale : ∀ r : ℝ, 0 < r → ∀ A : Set (Fin N → ℝ),
      volume ((G.dilate r) '' A) = ENNReal.ofReal (r ^ G.homogeneousDimension) * volume A)
    {ν : (Fin N → ℝ) → ℝ} (hν : G.IsHomogeneousGauge ν)
    (x : Fin N → ℝ) {r : ℝ} (hr : 0 < r) :
    volume {y : Fin N → ℝ | gaugeDistance G ν y x = r} = 0 := by
  have hs : {y : Fin N → ℝ | gaugeDistance G ν y x = r} =
      gaugeClosedBall G ν x r \ gaugeBall G ν x r := by
    ext y
    change gaugeDistance G ν y x = r ↔
      gaugeDistance G ν y x ≤ r ∧ ¬gaugeDistance G ν y x < r
    rw [not_lt]
    exact ⟨fun h => ⟨h.le, h.ge⟩, fun h => le_antisymm h.1 h.2⟩
  rw [hs, measure_sdiff]
  · rw [volume_gaugeClosedBall_of_volumeScaling htranslate hscale hν x hr, tsub_self]
  · intro y hy
    change gaugeDistance G ν y x ≤ r
    have hy' : gaugeDistance G ν y x < r := hy
    exact hy'.le
  · exact (isOpen_gaugeBall G hν x r).measurableSet.nullMeasurableSet
  · exact volume_gaugeBall_ne_top G hν x r

end RothschildStein.G2
