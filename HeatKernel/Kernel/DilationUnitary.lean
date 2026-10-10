-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Kernel.DilationPullback
public import Mathlib.MeasureTheory.Measure.QuasiMeasurePreserving

/-! # The unitary action of positive dilations

Normalized pullback is linear, preserves the inner product, and has reciprocal
dilation as its inverse.
-/

@[expose] public section

noncomputable section

open MeasureTheory

namespace HeatKernel

open RothschildStein

/-- Positive group dilations preserve volume null sets under pullback. -/
theorem quasiMeasurePreserving_group_dilate {n : ℕ} (G : HomogeneousGroup n)
    {r : ℝ} (hr : 0 < r) :
    Measure.QuasiMeasurePreserving (G.dilate r) volume volume := by
  refine ⟨(G2.continuous_dilate G r).measurable, ?_⟩
  rw [G2.map_dilate_volume G hr]
  exact Measure.smul_absolutelyContinuous

/-- Normalized dilation is a linear isometry on real L². -/
def dilationL2Isometry {n : ℕ} (G : HomogeneousGroup n) {r : ℝ} (hr : 0 < r) :
    Lp ℝ 2 (volume : Measure (Fin n → ℝ)) →ₗᵢ[ℝ]
      Lp ℝ 2 (volume : Measure (Fin n → ℝ)) := by
  let L : Lp ℝ 2 (volume : Measure (Fin n → ℝ)) →ₗ[ℝ]
      Lp ℝ 2 (volume : Measure (Fin n → ℝ)) :=
    { toFun := normalizedDilationL2 G hr
      map_add' := by
        intro f g
        apply Lp.ext
        filter_upwards [ae_normalizedDilationL2 G hr (f + g),
          ae_normalizedDilationL2 G hr f, ae_normalizedDilationL2 G hr g,
          (quasiMeasurePreserving_group_dilate G hr).ae_eq_comp (Lp.coeFn_add f g),
          Lp.coeFn_add (normalizedDilationL2 G hr f) (normalizedDilationL2 G hr g)]
          with x hsum hf hg hadd hout
        simp only [Function.comp_apply, Pi.add_apply] at hadd hout
        rw [hsum, hout, hf, hg]
        rw [hadd]
        exact mul_add _ _ _
      map_smul' := by
        intro c f
        apply Lp.ext
        filter_upwards [ae_normalizedDilationL2 G hr (c • f), ae_normalizedDilationL2 G hr f,
          (quasiMeasurePreserving_group_dilate G hr).ae_eq_comp (Lp.coeFn_smul c f),
          Lp.coeFn_smul c (normalizedDilationL2 G hr f)] with x hcf hf hsmul hout
        simp only [Function.comp_apply, Pi.smul_apply, smul_eq_mul] at hsmul hout
        change normalizedDilationL2 G hr (c • f) x = (c • normalizedDilationL2 G hr f) x
        rw [hcf, hout, hf]
        rw [hsmul]
        ring }
  exact L.isometryOfInner (inner_normalizedDilationL2 G hr)

/-- Reciprocal normalized dilation cancels positive normalized dilation. -/
theorem normalizedDilationL2_inv {n : ℕ} (G : HomogeneousGroup n)
    {r : ℝ} (hr : 0 < r) (f : Lp ℝ 2 (volume : Measure (Fin n → ℝ))) :
    normalizedDilationL2 G hr (normalizedDilationL2 G (inv_pos.mpr hr) f) = f := by
  apply Lp.ext
  filter_upwards [ae_normalizedDilationL2 G hr (normalizedDilationL2 G (inv_pos.mpr hr) f),
    (quasiMeasurePreserving_group_dilate G hr).ae_eq_comp
      (ae_normalizedDilationL2 G (inv_pos.mpr hr) f)] with x hout hin
  simp only [Function.comp_apply] at hin
  rw [hout, hin]
  simp only [inv_pow, Real.sqrt_inv, G2.dilate_inv_dilate G hr.ne']
  rw [← mul_assoc, mul_inv_cancel₀ (ne_of_gt (Real.sqrt_pos.mpr (pow_pos hr _))), one_mul]

/-- Positive group dilation acts by a unitary equivalence on real L². -/
def dilationL2Equiv {n : ℕ} (G : HomogeneousGroup n) {r : ℝ} (hr : 0 < r) :
    Lp ℝ 2 (volume : Measure (Fin n → ℝ)) ≃ₗᵢ[ℝ]
      Lp ℝ 2 (volume : Measure (Fin n → ℝ)) :=
  LinearIsometryEquiv.ofSurjective (dilationL2Isometry G hr) (fun f =>
    ⟨normalizedDilationL2 G (inv_pos.mpr hr) f, normalizedDilationL2_inv G hr f⟩)

/-- The unitary dilation has the normalized pullback representative. -/
theorem ae_dilationL2Equiv_apply {n : ℕ} (G : HomogeneousGroup n)
    {r : ℝ} (hr : 0 < r) (f : Lp ℝ 2 (volume : Measure (Fin n → ℝ))) :
    dilationL2Equiv G hr f =ᵐ[volume]
      fun x => Real.sqrt (r ^ G.homogeneousDimension) * f (G.dilate r x) :=
  ae_normalizedDilationL2 G hr f

end HeatKernel
