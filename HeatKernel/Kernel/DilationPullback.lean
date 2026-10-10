-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import Mathlib.MeasureTheory.Function.L2Space
public import RothschildStein.G2.DilationMeasure

/-! # Normalized dilation pullback on L²

The Haar Jacobian determines the square-root normalization that preserves the
L² inner product under positive group dilations.
-/

@[expose] public section

noncomputable section

open MeasureTheory

namespace HeatKernel

open RothschildStein

/-- Pullback by a positive group dilation preserves membership in L². -/
theorem memLp_comp_group_dilate {n : ℕ} (G : HomogeneousGroup n)
    {r : ℝ} (hr : 0 < r) (f : Lp ℝ 2 (volume : Measure (Fin n → ℝ))) :
    MemLp (fun x => f (G.dilate r x)) 2 volume := by
  have hf := (Lp.memLp f).smul_measure
    (c := ENNReal.ofReal ((r ^ G.homogeneousDimension)⁻¹)) ENNReal.ofReal_ne_top
  rw [← G2.map_dilate_volume G hr] at hf
  exact hf.comp_of_map (G2.continuous_dilate G r).measurable.aemeasurable

/-- Normalized dilation of an L² class, with normalization given by the Haar Jacobian. -/
def normalizedDilationL2 {n : ℕ} (G : HomogeneousGroup n)
    {r : ℝ} (hr : 0 < r) (f : Lp ℝ 2 (volume : Measure (Fin n → ℝ))) :
    Lp ℝ 2 (volume : Measure (Fin n → ℝ)) :=
  ((memLp_comp_group_dilate G hr f).const_mul (Real.sqrt (r ^ G.homogeneousDimension))).toLp
    (fun x => Real.sqrt (r ^ G.homogeneousDimension) * f (G.dilate r x))

/-- Normalized dilation has the expected almost-everywhere formula. -/
theorem ae_normalizedDilationL2 {n : ℕ} (G : HomogeneousGroup n)
    {r : ℝ} (hr : 0 < r) (f : Lp ℝ 2 (volume : Measure (Fin n → ℝ))) :
    normalizedDilationL2 G hr f =ᵐ[volume]
      fun x => Real.sqrt (r ^ G.homogeneousDimension) * f (G.dilate r x) :=
  MemLp.coeFn_toLp _

/-- The square-root Haar normalization makes positive dilation preserve inner products. -/
theorem inner_normalizedDilationL2 {n : ℕ} (G : HomogeneousGroup n)
    {r : ℝ} (hr : 0 < r) (f g : Lp ℝ 2 (volume : Measure (Fin n → ℝ))) :
    inner ℝ (normalizedDilationL2 G hr f) (normalizedDilationL2 G hr g) = inner ℝ f g := by
  rw [L2.inner_def, L2.inner_def]
  have heq : (∫ x, inner ℝ (normalizedDilationL2 G hr f x)
      (normalizedDilationL2 G hr g x)) =
      (r ^ G.homogeneousDimension) * ∫ x, f (G.dilate r x) * g (G.dilate r x) := by
    calc
      _ = ∫ x, (r ^ G.homogeneousDimension) *
          (f (G.dilate r x) * g (G.dilate r x)) := by
        apply integral_congr_ae
        filter_upwards [ae_normalizedDilationL2 G hr f, ae_normalizedDilationL2 G hr g]
          with x hf hg
        rw [hf, hg, Real.inner_apply]
        calc
          _ = (Real.sqrt (r ^ G.homogeneousDimension)) ^ 2 *
              (f (G.dilate r x) * g (G.dilate r x)) := by ring
          _ = _ := by rw [Real.sq_sqrt (pow_pos hr G.homogeneousDimension).le]
      _ = _ := integral_const_mul _ _
  rw [heq]
  have hd := G2.integral_dilate G hr (fun x => f x * g x)
  rw [hd, smul_eq_mul, ← mul_assoc, mul_inv_cancel₀ (pow_ne_zero _ hr.ne'), one_mul]
  simp only [Real.inner_apply]

end HeatKernel
