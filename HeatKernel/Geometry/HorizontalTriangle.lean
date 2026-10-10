-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Geometry.CurveConcatenation

/-! The triangle inequality for the horizontal control distance. -/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set MeasureTheory
open scoped BigOperators NNReal
namespace HeatKernel

private theorem measurePreserving_unit_shift :
    MeasurePreserving (fun u : ℝ => u - 1)
      (volume.restrict (Icc 1 2)) (volume.restrict (Icc 0 1)) := by
  have hp : (fun u : ℝ => u - 1) ⁻¹' Icc 0 1 = Icc 1 2 := by
    ext u
    simp only [mem_preimage, mem_Icc]
    constructor <;> rintro ⟨h₁, h₂⟩ <;> constructor <;> linarith
  have hm : MeasurePreserving (fun u : ℝ => u - 1) volume volume := by
    simpa only [sub_eq_add_neg] using measurePreserving_add_right volume (-1 : ℝ)
  simpa only [hp] using hm.restrict_preimage
    (measurableSet_Icc : MeasurableSet (Icc (0 : ℝ) 1))

/-- Moving a curve from the unit interval to the next unit interval preserves horizontality. -/
theorem IsHorizontalCurveOn.unit_shift {N q : ℕ}
    {X : Fin q → (Fin N → ℝ) → (Fin N → ℝ)} {γ : ℝ → (Fin N → ℝ)}
    {a : Fin q → ℝ → ℝ} (h : IsHorizontalCurveOn X γ a 0 1) :
    IsHorizontalCurveOn X (fun u => γ (u - 1)) (fun i u => a i (u - 1)) 1 2 := by
  have hmp := measurePreserving_unit_shift
  have hK : LipschitzOnWith 1 (fun u : ℝ => u - 1) (uIcc 1 2) := by
    apply LipschitzOnWith.of_dist_le_mul
    intro u _ v _
    simp only [NNReal.coe_one, one_mul, Real.dist_eq]
    rw [show u - 1 - (v - 1) = u - v by ring]
  refine ⟨absolutelyContinuousOnInterval_comp_of_monotone h.absolutelyContinuous
    (Or.inl (by intro u v huv; dsimp; linarith))
    hK ?_,
    fun i => (h.aemeasurable i).comp_quasiMeasurePreserving hmp.quasiMeasurePreserving,
    hmp.integrable_comp_of_integrable h.integrable_norm, ?_⟩
  · intro u hu
    simp only [uIcc_of_le (by norm_num : (1 : ℝ) ≤ 2), mem_Icc] at hu
    simp only [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1), mem_Icc]
    constructor <;> linarith [hu.1, hu.2]
  · filter_upwards [hmp.quasiMeasurePreserving.ae h.hasDerivAt] with u hu
    simpa only [Function.comp_def, one_smul, id_eq] using
      hu.scomp u ((hasDerivAt_id u).sub_const 1)

/-- Translation of the second unit interval preserves the integrated control norm. -/
theorem controlLength_unit_shift {q : ℕ} (a : Fin q → ℝ → ℝ) :
    (∫ u in Icc (1 : ℝ) 2, controlNorm (fun i v => a i (v - 1)) u) =
      ∫ u in Icc (0 : ℝ) 1, controlNorm a u :=
  measurePreserving_unit_shift.integral_comp
    (Homeomorph.subRight (1 : ℝ)).measurableEmbedding (controlNorm a)

/-- The length of concatenated horizontal controls is the sum of the two lengths. -/
theorem controlLength_append {q : ℕ} (a b : Fin q → ℝ → ℝ) {s c t : ℝ}
    (hsc : s ≤ c) (hct : c ≤ t)
    (ha : IntegrableOn (controlNorm a) (Icc s c))
    (hb : IntegrableOn (controlNorm b) (Icc c t)) :
    (∫ u in Icc s t, controlNorm (fun i v => if v ≤ c then a i v else b i v) u) =
      (∫ u in Icc s c, controlNorm a u) + ∫ u in Icc c t, controlNorm b u := by
  let L := controlNorm (fun i v => if v ≤ c then a i v else b i v)
  have he₁ : L =ᵐ[volume.restrict (Icc s c)] controlNorm a := by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with u hu
    simp only [L, controlNorm, ite_eq_left hu.2]
  have he₂ : L =ᵐ[volume.restrict (Icc c t)] controlNorm b := by
    filter_upwards [ae_restrict_mem measurableSet_Icc,
      (volume.restrict (Icc c t)).ae_ne c] with u hu hne
    simp only [L, controlNorm, ite_eq_right (not_le.mpr (lt_of_le_of_ne hu.1 (Ne.symm hne)))]
  have hd : AEDisjoint volume (Icc s c) (Icc c t) := by
    apply measure_mono_null (t := {c})
    · intro u hu
      simp only [mem_singleton_iff]
      exact le_antisymm hu.1.2 hu.2.1
    · exact measure_singleton c
  change (∫ u in Icc s t, L u) = _
  rw [← Icc_union_Icc_eq_Icc hsc hct,
    setIntegral_union₀ hd measurableSet_Icc.nullMeasurableSet
      (ha.congr he₁.symm) (hb.congr he₂.symm), integral_congr_ae he₁, integral_congr_ae he₂]

/-- Concatenating horizontal competitors proves the triangle inequality, including
infinite distances. -/
theorem horizontalL2Distance_triangle {N q : ℕ}
    (X : Fin q → (Fin N → ℝ) → (Fin N → ℝ)) (x y z : Fin N → ℝ) :
    horizontalL2Distance X x z ≤ horizontalL2Distance X x y + horizontalL2Distance X y z := by
  unfold horizontalL2Distance
  rw [ENNReal.sInf_add]
  apply le_iInf₂
  rintro r ⟨f, a, hfac, hfx, hfy, hfa, hfi, hfd, rfl⟩
  rw [ENNReal.add_sInf]
  apply le_iInf₂
  rintro r ⟨g, b, hgac, hgy, hgz, hga, hgi, hgd, rfl⟩
  have hf : IsHorizontalCurveOn X f a 0 1 := ⟨hfac, hfa, hfi, hfd⟩
  have hg : IsHorizontalCurveOn X g b 0 1 := ⟨hgac, hga, hgi, hgd⟩
  have hc := hf.append hg.unit_shift (by norm_num) (by norm_num)
    (by simp only [sub_self, hfy, hgy])
  have hd := hc.distance_le_controlLength (by norm_num)
  rw [controlLength_append a (fun i u => b i (u - 1)) (by norm_num) (by norm_num)
    hf.integrable_norm hg.unit_shift.integrable_norm, controlLength_unit_shift] at hd
  have hna : 0 ≤ ∫ u in Icc (0 : ℝ) 1, controlNorm a u :=
    integral_nonneg fun u => Real.sqrt_nonneg _
  have hnb : 0 ≤ ∫ u in Icc (0 : ℝ) 1, controlNorm b u :=
    integral_nonneg fun u => Real.sqrt_nonneg _
  rw [ENNReal.ofReal_add hna hnb] at hd
  simpa only [ite_eq_left (by norm_num : (0 : ℝ) ≤ 1),
    ite_eq_right (by norm_num : ¬(2 : ℝ) ≤ 1), show (2 : ℝ) - 1 = 1 by norm_num,
    hfx, hgz, controlNorm, horizontalL2Distance] using hd

end HeatKernel
