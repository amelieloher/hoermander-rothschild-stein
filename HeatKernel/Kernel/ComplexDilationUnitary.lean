-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Kernel.ComplexDilationPullback

/-! # Complex unitary dilation and real embedding compatibility

Reciprocal normalized dilation is the inverse of positive normalized dilation.
The resulting complex unitary intertwines the real action whenever the real
embedding has its scalar almost-everywhere representative formula.
-/

@[expose] public section

noncomputable section

open MeasureTheory RothschildStein

namespace HeatKernel

/-- Positive normalized dilation is a complex linear isometry. -/
def complexDilationL2Isometry {n : ℕ} (G : HomogeneousGroup n) {r : ℝ} (hr : 0 < r) :
    Lp ℂ 2 (volume : Measure (Fin n → ℝ)) →ₗᵢ[ℂ] Lp ℂ 2 (volume : Measure (Fin n → ℝ)) :=
  (complexNormalizedDilationL2 G hr).toLinearMap.isometryOfInner
    (inner_complexNormalizedDilationL2 G hr)

/-- Reciprocal normalized complex dilation cancels positive normalized dilation. -/
theorem complexNormalizedDilationL2_inv {n : ℕ} (G : HomogeneousGroup n)
    {r : ℝ} (hr : 0 < r) (f : Lp ℂ 2 (volume : Measure (Fin n → ℝ))) :
    complexNormalizedDilationL2 G hr (complexNormalizedDilationL2 G (inv_pos.mpr hr) f) = f := by
  have hreal : Real.sqrt (r ^ G.homogeneousDimension) *
      Real.sqrt ((r⁻¹) ^ G.homogeneousDimension) = 1 := by
    rw [inv_pow, Real.sqrt_inv, mul_inv_cancel₀ (ne_of_gt (Real.sqrt_pos.mpr (pow_pos hr _)))]
  have hscalar : (Real.sqrt (r ^ G.homogeneousDimension) : ℂ) *
      (Real.sqrt ((r⁻¹) ^ G.homogeneousDimension) : ℂ) = 1 := by
    rw [← Complex.ofReal_mul, hreal, Complex.ofReal_one]
  apply Lp.ext
  filter_upwards [ae_complexNormalizedDilationL2 G hr (complexNormalizedDilationL2 G (inv_pos.mpr hr) f),
    (quasiMeasurePreserving_group_dilate G hr).ae_eq_comp
      (ae_complexNormalizedDilationL2 G (inv_pos.mpr hr) f)] with x hout hin
  change complexNormalizedDilationL2 G (inv_pos.mpr hr) f (G.dilate r x) =
    (Real.sqrt ((r⁻¹) ^ G.homogeneousDimension) : ℂ) * f (G.dilate r⁻¹ (G.dilate r x)) at hin
  rw [hout, hin, G2.dilate_inv_dilate G hr.ne', ← mul_assoc, hscalar, one_mul]

/-- Positive group dilation acts by a complex unitary equivalence. -/
def complexDilationL2Equiv {n : ℕ} (G : HomogeneousGroup n) {r : ℝ} (hr : 0 < r) :
    Lp ℂ 2 (volume : Measure (Fin n → ℝ)) ≃ₗᵢ[ℂ] Lp ℂ 2 (volume : Measure (Fin n → ℝ)) :=
  LinearIsometryEquiv.ofSurjective (complexDilationL2Isometry G hr) (fun f =>
    ⟨complexNormalizedDilationL2 G (inv_pos.mpr hr) f, complexNormalizedDilationL2_inv G hr f⟩)

/-- The complex unitary dilation has its normalized pullback representative. -/
theorem ae_complexDilationL2Equiv_apply {n : ℕ} (G : HomogeneousGroup n) {r : ℝ} (hr : 0 < r)
    (f : Lp ℂ 2 (volume : Measure (Fin n → ℝ))) :
    complexDilationL2Equiv G hr f =ᵐ[volume]
      fun x => (Real.sqrt (r ^ G.homogeneousDimension) : ℂ) * f (G.dilate r x) :=
  ae_complexNormalizedDilationL2 G hr f

/-- The real and complex normalized dilations intertwine through an embedding with its scalar real representative formula. -/
theorem complexDilationL2Equiv_apply_real_embedding {n : ℕ}
    (G : HomogeneousGroup n) {r : ℝ} (hr : 0 < r)
    (j : Lp ℝ 2 (volume : Measure (Fin n → ℝ)) → Lp ℂ 2 (volume : Measure (Fin n → ℝ)))
    (hj : ∀ f, j f =ᵐ[volume] fun x => (f x : ℂ))
    (f : Lp ℝ 2 (volume : Measure (Fin n → ℝ))) :
    complexDilationL2Equiv G hr (j f) = j (dilationL2Equiv G hr f) := by
  apply Lp.ext
  filter_upwards [ae_complexDilationL2Equiv_apply G hr (j f),
    (quasiMeasurePreserving_group_dilate G hr).ae_eq_comp (hj f),
    hj (dilationL2Equiv G hr f), ae_dilationL2Equiv_apply G hr f] with x hdilate hcomp hjdilate hreal
  change j f (G.dilate r x) = (f (G.dilate r x) : ℂ) at hcomp
  rw [hdilate, hcomp, hjdilate, hreal, Complex.ofReal_mul]

end HeatKernel
