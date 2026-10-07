-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.G2.SphereMeasure

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
open Set MeasureTheory
open scoped BigOperators ENNReal
namespace RothschildStein.G2

private theorem measure_ext_Iio_finite (μ σ : Measure ℝ)
    (hfinite : ∀ r : ℝ, μ (Iio r) ≠ ⊤)
    (heq : ∀ r : ℝ, μ (Iio r) = σ (Iio r)) : μ = σ := by
  apply Measure.ext_of_Ico' μ σ
  · intro a b _
    exact ne_top_of_le_ne_top (hfinite b) (measure_mono fun _ hx => hx.2)
  · intro a b hab
    have hset : Ico a b = Iio b \ Iio a := by
      ext x
      simp only [mem_Ico, mem_sdiff, mem_Iio, not_lt]
      exact and_comm
    have hsub : Iio a ⊆ Iio b := fun _ hx => lt_of_lt_of_le hx hab.le
    rw [hset, measure_sdiff hsub measurableSet_Iio.nullMeasurableSet (hfinite a),
      measure_sdiff hsub measurableSet_Iio.nullMeasurableSet
        (by rw [← heq a]; exact hfinite a), heq a, heq b]

private theorem root_map_Iio {Q : ℕ} (hQ : 0 < Q) (r : ℝ) :
    (Measure.map (fun t : ℝ => t ^ ((Q : ℝ)⁻¹)) (volume.restrict (Ioi 0))) (Iio r) =
      if 0 < r then ENNReal.ofReal (r ^ Q) else 0 := by
  have hp : 0 < (Q : ℝ)⁻¹ := inv_pos.mpr (Nat.cast_pos.mpr hQ)
  have hc : Measurable (fun t : ℝ => t ^ ((Q : ℝ)⁻¹)) :=
    (Real.continuous_rpow_const hp.le).measurable
  rw [Measure.map_apply hc measurableSet_Iio, Measure.restrict_apply (hc measurableSet_Iio)]
  by_cases hr : 0 < r
  · rw [ite_eq_left hr]
    have hset : ((fun t : ℝ => t ^ ((Q : ℝ)⁻¹)) ⁻¹' Iio r) ∩ Ioi 0 = Ioo 0 (r ^ Q) := by
      ext t
      constructor
      · rintro ⟨ht, ht0⟩
        exact ⟨ht0, by simpa only [Real.rpow_natCast] using
          (Real.rpow_inv_lt_iff_of_pos ht0.le hr.le (Nat.cast_pos.mpr hQ)).mp ht⟩
      · rintro ⟨ht0, ht⟩
        exact ⟨(Real.rpow_inv_lt_iff_of_pos ht0.le hr.le (Nat.cast_pos.mpr hQ)).mpr
          (by simpa only [Real.rpow_natCast] using ht), ht0⟩
    rw [hset]
    simp
  · rw [ite_eq_right hr]
    have hset : ((fun t : ℝ => t ^ ((Q : ℝ)⁻¹)) ⁻¹' Iio r) ∩ Ioi 0 = ∅ := by
      ext t
      simp only [mem_inter_iff, mem_preimage, mem_Iio, mem_Ioi, mem_empty_iff_false, iff_false]
      rintro ⟨ht, ht0⟩
      exact hr ((Real.rpow_pos_of_pos ht0 _).trans ht)
    rw [hset, measure_empty]

/-- The radial pushforward is the scaled root image of one-dimensional Lebesgue measure under dilation-volume scaling. This identifies the measure before radial change of variables (BB Proposition 3.21, pp. 105–106). -/
theorem radial_pushforward_of_volumeScaling {N : ℕ} {G : HomogeneousGroup N}
    (hscale : ∀ r : ℝ, 0 < r → ∀ A : Set (Fin N → ℝ),
      volume ((G.dilate r) '' A) = ENNReal.ofReal (r ^ G.homogeneousDimension) * volume A)
    {ν : (Fin N → ℝ) → ℝ} (hν : G.IsHomogeneousGauge ν) :
    Measure.map ν volume = volume {u : Fin N → ℝ | ν u < 1} •
      Measure.map (fun t : ℝ => t ^ ((G.homogeneousDimension : ℝ)⁻¹)) (volume.restrict (Ioi 0)) := by
  have hQ : 0 < G.homogeneousDimension := by
    unfold HomogeneousGroup.homogeneousDimension
    exact Finset.sum_pos (fun j _ => G.weight_pos j)
      (Finset.univ_nonempty_iff.mpr ⟨⟨0, G.dimension_pos⟩⟩)
  let m := volume {u : Fin N → ℝ | ν u < 1}
  have hm : m ≠ ⊤ := ne_top_of_le_ne_top ((isCompact_gauge_le hν 1).measure_ne_top (μ := volume))
    (measure_mono fun x (hx : ν x < 1) => hx.le)
  have hCDF (r : ℝ) : (Measure.map ν volume) (Iio r) =
      if 0 < r then ENNReal.ofReal (r ^ G.homogeneousDimension) * m else 0 := by
    rw [Measure.map_apply hν.1.measurable measurableSet_Iio]
    by_cases hr : 0 < r
    · rw [ite_eq_left hr]
      change volume {u : Fin N → ℝ | ν u < r} = _
      rw [gauge_sublevel_dilate hν hr, hscale r hr]
    · rw [ite_eq_right hr]
      have he : ν ⁻¹' Iio r = ∅ := by
        ext x
        simp only [mem_preimage, mem_Iio, mem_empty_iff_false, iff_false]
        intro hx
        exact hr (lt_of_le_of_lt (hν.2.1 x) hx)
      rw [he, measure_empty]
  apply measure_ext_Iio_finite
  · intro r
    rw [hCDF]
    split_ifs
    · exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top hm
    · simp
  · intro r
    rw [hCDF, Measure.smul_apply, root_map_Iio hQ]
    split_ifs <;> simp [m, smul_eq_mul, mul_comm]

end RothschildStein.G2
