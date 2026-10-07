-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.G1.ControlledReparam
public import RothschildStein.G1.AbsoluteContinuityGlue
public import RothschildStein.G1.MeasurableControls

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set Filter MeasureTheory MeasureTheory.Measure
open scoped Topology BigOperators

namespace RothschildStein.G1

/-- Join two curves at an interior time (BB Prop 1.36, p. 19). -/
def joinedCurve {E : Type*} (θ : ℝ) (γ η : ℝ → E) (t : ℝ) : E :=
  if t ≤ θ then γ (t / θ) else η ((t - θ) / (1 - θ))

/-- Affine rescaling of both pieces preserves absolute continuity at
the common endpoint (BB Prop 1.36, p. 19). -/
theorem joinedCurve_absolutelyContinuous {E : Type*} [SeminormedAddCommGroup E]
    {θ : ℝ} (hθ : 0 < θ) (hθ1 : θ < 1) {γ η : ℝ → E}
    (hγ : AbsolutelyContinuousOnInterval γ 0 1)
    (hη : AbsolutelyContinuousOnInterval η 0 1) (hends : γ 1 = η 0) :
    AbsolutelyContinuousOnInterval (joinedCurve θ γ η) 0 1 := by
  have hθn : θ ≠ 0 := ne_of_gt hθ
  have hcn : 1 - θ ≠ 0 := ne_of_gt (sub_pos.mpr hθ1)
  have hleft : AbsolutelyContinuousOnInterval (fun t => γ (t / θ)) 0 θ := by
    have hh := absolutelyContinuousOnInterval_comp_affine (c := 0) (d := 1 / θ)
      (a := 0) (b := θ) (one_div_ne_zero hθn)
      (by simpa [hθn] using hγ)
    simpa only [zero_add, one_div_mul_eq_div] using hh
  have hright : AbsolutelyContinuousOnInterval (fun t => η ((t - θ) / (1 - θ))) θ 1 := by
    have he : ∀ t : ℝ, -θ / (1 - θ) + (1 / (1 - θ)) * t = (t - θ) / (1 - θ) := by
      intro t; ring
    have hh := absolutelyContinuousOnInterval_comp_affine (c := -θ / (1 - θ))
      (d := 1 / (1 - θ)) (a := θ) (b := 1) (one_div_ne_zero hcn)
      (by simpa only [he, sub_self, zero_div, div_self hcn] using hη)
    simpa only [he] using hh
  apply absolutelyContinuousOnInterval_glue hθ.le hθ1.le
  · apply hleft.congr
    intro t ht
    simp only [uIcc_of_le hθ.le] at ht
    simp only [joinedCurve, ite_eq_left ht.2]
  · apply hright.congr
    intro t ht
    simp only [uIcc_of_le hθ1.le] at ht
    by_cases h : t ≤ θ
    · have he : t = θ := le_antisymm h ht.1
      subst t
      simp only [joinedCurve, ite_eq_left le_rfl, div_self hθn, sub_self, zero_div, hends]
    · simp only [joinedCurve, ite_eq_right h]

/-- Actual controlled-curve concatenation with explicit rescaled
weight bounds. The join point is excluded only from the a.e. derivative
statement (BB Prop 1.36, p. 19). -/
theorem isControlledCurve_join {m n : ℕ} {Ω : Set (Fin n → ℝ)}
    {w : Fin m → ℕ+} {X : Fin m → (Fin n → ℝ) → (Fin n → ℝ)}
    {δ ε ρ θ : ℝ} {γ η : ℝ → (Fin n → ℝ)}
    (hγ : isControlledCurve Ω w X δ γ) (hη : isControlledCurve Ω w X ε η)
    (hends : γ 1 = η 0) (hθ : 0 < θ) (hθ1 : θ < 1) (hρ : 0 < ρ)
    (hleft : ∀ i, δ ^ (w i : ℕ) / θ ≤ ρ ^ (w i : ℕ))
    (hright : ∀ i, ε ^ (w i : ℕ) / (1 - θ) ≤ ρ ^ (w i : ℕ)) :
    isControlledCurve Ω w X ρ (joinedCurve θ γ η) := by
  obtain ⟨a, hma, ha⟩ := isControlledCurve_measurable_controls hγ
  obtain ⟨b, hmb, hb⟩ := isControlledCurve_measurable_controls hη
  have hc : 0 < 1 - θ := sub_pos.mpr hθ1
  have hmapL : MapsTo (fun t : ℝ => t / θ) (Icc 0 θ) (Icc 0 1) := by
    intro t ht
    exact ⟨div_nonneg ht.1 hθ.le, (div_le_one hθ).mpr ht.2⟩
  have hmapR : MapsTo (fun t : ℝ => (t - θ) / (1 - θ)) (Icc θ 1) (Icc 0 1) := by
    intro t ht
    exact ⟨div_nonneg (sub_nonneg.mpr ht.1) hc.le, (div_le_one hc).mpr (by linarith [ht.2])⟩
  have hqL : QuasiMeasurePreserving (fun t : ℝ => t / θ)
      (volume.restrict (Icc 0 θ)) (volume.restrict (Icc (0 : ℝ) 1)) := by
    have hh := (quasiMeasurePreserving_smul volume (one_div_ne_zero (ne_of_gt hθ))).restrict
      (show MapsTo (fun t : ℝ => (1 / θ) • t) (Icc 0 θ) (Icc 0 1) by
        simpa only [smul_eq_mul, one_div_mul_eq_div] using hmapL)
    simpa only [smul_eq_mul, one_div_mul_eq_div] using hh
  have hqR : QuasiMeasurePreserving (fun t : ℝ => (t - θ) / (1 - θ))
      (volume.restrict (Icc θ 1)) (volume.restrict (Icc (0 : ℝ) 1)) := by
    have hh := (quasiMeasurePreserving_smul volume (one_div_ne_zero (ne_of_gt hc))).comp
      (quasiMeasurePreserving_add_right volume (-θ))
    have he : (fun t : ℝ => (1 / (1 - θ)) • (t + -θ)) = (fun t => (t - θ) / (1 - θ)) := by
      funext t; simp only [smul_eq_mul, one_div_mul_eq_div, sub_eq_add_neg]
    simp only [Function.comp_def] at hh
    rw [he] at hh
    exact hh.restrict hmapR
  let c : Fin m → ℝ → ℝ := fun i t =>
    if t ≤ θ then a i (t / θ) / θ else b i ((t - θ) / (1 - θ)) / (1 - θ)
  have hmc : ∀ i, Measurable (c i) := by
    intro i
    exact (((hma i).comp (by fun_prop)).div_const θ).piecewise measurableSet_Iic
      (((hmb i).comp (by fun_prop)).div_const (1 - θ))
  have hrange : MapsTo (joinedCurve θ γ η) (Icc 0 1) Ω := by
    intro t ht
    by_cases h : t ≤ θ
    · simpa only [joinedCurve, ite_eq_left h] using hγ.2.2.1 (hmapL ⟨ht.1, h⟩)
    · simpa only [joinedCurve, ite_eq_right h] using hη.2.2.1 (hmapR ⟨le_of_not_ge h, ht.2⟩)
  refine ⟨hρ, joinedCurve_absolutelyContinuous hθ hθ1 hγ.2.1 hη.2.1 hends,
    hrange, c, fun i => (hmc i).aemeasurable, ?_⟩
  have ha' := (ae_restrict_iff' measurableSet_Icc).mp (hqL.ae ha)
  have hb' := (ae_restrict_iff' measurableSet_Icc).mp (hqR.ae hb)
  filter_upwards [ae_restrict_of_ae ha', ae_restrict_of_ae hb',
    ae_restrict_mem measurableSet_Icc, ae_restrict_of_ae (volume.ae_ne θ)] with t hat hbt ht hne
  by_cases h : t ≤ θ
  · have hlt : t < θ := lt_of_le_of_ne h hne
    have hact := hat ⟨ht.1, h⟩
    have hderiv := hact.2.scomp t ((hasDerivAt_id t).div_const θ)
    have heq : joinedCurve θ γ η =ᶠ[𝓝 t] (fun v => γ (v / θ)) := by
      filter_upwards [Iio_mem_nhds hlt] with v hv
      exact ite_eq_left (le_of_lt hv)
    refine ⟨fun i => ?_, ?_⟩
    · simp only [c, ite_eq_left h]
      rw [abs_div, abs_of_pos hθ]
      exact (div_le_div_of_nonneg_right (hact.1 i) hθ.le).trans (hleft i)
    · simpa only [joinedCurve, c, ite_eq_left h, Finset.smul_sum, smul_smul,
        div_eq_mul_inv, one_mul, mul_one, mul_comm] using hderiv.congr_of_eventuallyEq heq
  · have hgt : θ < t := lt_of_not_ge h
    have hact := hbt ⟨hgt.le, ht.2⟩
    have hderiv := hact.2.scomp t (((hasDerivAt_id t).sub_const θ).div_const (1 - θ))
    have heq : joinedCurve θ γ η =ᶠ[𝓝 t] (fun v => η ((v - θ) / (1 - θ))) := by
      filter_upwards [Ioi_mem_nhds hgt] with v hv
      exact ite_eq_right (not_le.mpr hv)
    refine ⟨fun i => ?_, ?_⟩
    · simp only [c, ite_eq_right h]
      rw [abs_div, abs_of_pos hc]
      exact (div_le_div_of_nonneg_right (hact.1 i) hc.le).trans (hright i)
    · simpa only [joinedCurve, c, ite_eq_right h, Finset.smul_sum, smul_smul,
        div_eq_mul_inv, one_mul, mul_one, mul_comm] using hderiv.congr_of_eventuallyEq heq

end RothschildStein.G1
