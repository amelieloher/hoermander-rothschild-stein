-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Geometry.ClockReparametrization
public import HeatKernel.Geometry.AffineReparametrization
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-! Horizontal curves with bounded controls obtained from regularized clocks. -/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set MeasureTheory Filter
open scoped BigOperators NNReal
namespace HeatKernel

/-- Division of all controls by a positive scalar divides their Euclidean norm. -/
theorem controlNorm_div {q : ℕ} (a : Fin q → ℝ → ℝ) (d : ℝ → ℝ) (u : ℝ) (hd : 0 < d u) :
    controlNorm (fun i v => a i v / d v) u = controlNorm a u / d u := by
  have hh := controlNorm_mul a (d u)⁻¹ u
  simp only [controlNorm] at hh ⊢
  simpa only [abs_of_pos (inv_pos.mpr hd), div_eq_mul_inv, mul_comm] using hh

/-- A regularized clock turns horizontal controls into controls of norm at most one,
without changing their integrated length. -/
theorem IsHorizontalCurveOn.normalize {N q : ℕ}
    {X : Fin q → (Fin N → ℝ) → (Fin N → ℝ)} {γ : ℝ → (Fin N → ℝ)}
    {a : Fin q → ℝ → ℝ} (h : IsHorizontalCurveOn X γ a 0 1)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ (e : ℝ ≃o ℝ) (b : Fin q → ℝ → ℝ),
      (∀ u, b u = fun t => a u (e.symm t) / (controlNorm a (e.symm t) + ε)) ∧
      IsHorizontalCurveOn X (γ ∘ e.symm) b (e 0) (e 1) ∧
      (∀ t, controlNorm b t ≤ 1) ∧
      (∫ t in Icc (e 0) (e 1), controlNorm b t) = ∫ t in Icc (0 : ℝ) 1, controlNorm a t ∧
      (∀ t ∈ Icc (0 : ℝ) 1, e t = ∫ u in Icc (0 : ℝ) t, controlNorm a u + ε) := by
  obtain ⟨e, he, hi⟩ := exists_regularized_integral_clock h.integrable_norm
    (Eventually.of_forall fun t => Real.sqrt_nonneg _) hε
  let w := fun t => controlNorm a t + ε
  have hw : IntegrableOn w (Icc (0 : ℝ) 1) :=
    h.integrable_norm.add (integrableOn_const (by simp [Real.volume_Icc]))
  have hp : ∀ t, 0 < w t := fun t => add_pos_of_nonneg_of_pos (Real.sqrt_nonneg _) hε
  have hq := quasiMeasurePreserving_inverse_clock hw (Eventually.of_forall fun t => (hp t).le) he
  let b := fun i t => a i (e.symm t) / w (e.symm t)
  let r := fun t => controlNorm a t / w t
  have hbnorm : ∀ t, controlNorm b t = r (e.symm t) := by
    intro t
    exact controlNorm_div (fun i v => a i (e.symm v)) (fun v => w (e.symm v)) t (hp _)
  have hr : AEMeasurable r (volume.restrict (Icc (0 : ℝ) 1)) :=
    h.integrable_norm.aestronglyMeasurable.aemeasurable.div hw.aestronglyMeasurable.aemeasurable
  have hbmeas : ∀ i, AEMeasurable (b i) (volume.restrict (Icc (e 0) (e 1))) := fun i =>
    ((h.aemeasurable i).div hw.aestronglyMeasurable.aemeasurable).comp_quasiMeasurePreserving hq
  have hnmeas : AEMeasurable (controlNorm b) (volume.restrict (Icc (e 0) (e 1))) := by
    apply (hr.comp_quasiMeasurePreserving hq).congr
    exact Eventually.of_forall fun t => (hbnorm t).symm
  have hbound : ∀ t, controlNorm b t ≤ 1 := by
    intro t
    rw [hbnorm]
    exact (div_le_one (hp _)).2 (le_add_of_nonneg_right hε.le)
  have hbint : IntegrableOn (controlNorm b) (Icc (e 0) (e 1)) := by
    apply (integrableOn_const (C := (1 : ℝ)) (by simp [Real.volume_Icc])).mono'
      hnmeas.aestronglyMeasurable
    exact Eventually.of_forall fun t => by
      rw [Real.norm_eq_abs, abs_of_nonneg (show 0 ≤ controlNorm b t from Real.sqrt_nonneg _)]
      exact hbound t
  refine ⟨e, b, fun _ => rfl, ⟨absolutelyContinuousOnInterval_comp_inverse_clock
    h.absolutelyContinuous (lipschitzWith_inverse_clock hε hi), hbmeas, hbint, ?_⟩, hbound, ?_, he⟩
  · filter_upwards [hq.ae h.hasDerivAt, ae_hasDerivAt_inverse_clock hw
      (Eventually.of_forall hp) he] with t ht hτ
    have hd := ht.scomp t hτ
    simpa only [Function.comp_def, b, div_eq_mul_inv, Finset.smul_sum,
      smul_smul, mul_comm] using hd
  · have hmap := map_inverse_clock_eq_withDensity e w hw
      (Eventually.of_forall fun t => (hp t).le) he
    have hm : AEStronglyMeasurable r ((volume.restrict (Icc (e 0) (e 1))).map e.symm) :=
      hr.aestronglyMeasurable.mono_ac hq.absolutelyContinuous
    simp_rw [hbnorm]
    rw [← integral_map e.symm.continuous.measurable.aemeasurable hm, hmap,
      integral_withDensity_eq_integral_toReal_smul₀ hw.aestronglyMeasurable.aemeasurable.ennreal_ofReal
        (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top) r]
    apply integral_congr_ae
    exact Eventually.of_forall fun t => by
      simp only [ENNReal.toReal_ofReal (hp t).le, smul_eq_mul, r]
      exact mul_div_cancel₀ _ (hp t).ne'

end HeatKernel
