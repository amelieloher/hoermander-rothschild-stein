-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import Hormander.B.Fractional.DiffOps
public import Hormander.A.Mollifier.Contraction

@[expose] public section

noncomputable section

open MeasureTheory
open scoped FourierTransform

namespace Hormander.B

variable {N : ℕ}

/-- The mollifier on Schwartz functions as a linear operator. -/
def mollOp (N : ℕ) (δ : ℝ) (hδ : 0 < δ) : Operator N :=
  (Hormander.A.SδSchwartz N δ hδ).toLinearMap

/-- The Fourier symbol of the mollifier at scale `δ`. -/
def mollSymbol (N : ℕ) (δ : ℝ) (hδ : 0 < δ) (ξ : Carrier N) : ℂ :=
  𝓕 (Hormander.A.Jδ N δ hδ) ξ

theorem fourier_mollOp (δ : ℝ) (hδ : 0 < δ) (u : TestFunction N) (ξ : Carrier N) :
    𝓕 (mollOp N δ hδ u) ξ = mollSymbol N δ hδ ξ * 𝓕 u ξ := by
  have h := SchwartzMap.fourier_convolution (ContinuousLinearMap.lsmul ℂ ℂ)
    (Hormander.A.Jδ N δ hδ) u
  change 𝓕 (SchwartzMap.convolution (ContinuousLinearMap.lsmul ℂ ℂ)
    (Hormander.A.Jδ N δ hδ) u) ξ = _
  rw [h, SchwartzMap.pairing_apply_apply]
  rfl

/-- Scaling of the mollifier symbol. -/
theorem mollSymbol_eq (δ : ℝ) (hδ : 0 < δ) (ξ : Carrier N) :
    mollSymbol N δ hδ ξ = 𝓕 (Hormander.A.Jc N) (δ • ξ) := by
  unfold mollSymbol
  rw [SchwartzMap.fourier_coe, SchwartzMap.fourier_coe, Real.fourier_eq', Real.fourier_eq']
  set f : Carrier N → ℂ := fun v =>
    Complex.exp (↑(-2 * Real.pi * inner ℝ v ξ) * Complex.I) * Hormander.A.Jc N (δ⁻¹ • v) with hf
  have h1 : ∫ v, Complex.exp (↑(-2 * Real.pi * inner ℝ v ξ) * Complex.I) •
      (Hormander.A.Jδ N δ hδ) v = ((δ ^ N : ℝ)⁻¹ : ℝ) • ∫ v, f v := by
    rw [← integral_smul]
    congr 1; funext v
    simp only [Hormander.A.Jδ_apply, hf, smul_eq_mul, Complex.real_smul]
    ring
  have h2 : ∫ v, f v = (δ ^ N : ℝ) • ∫ y, Complex.exp (↑(-2 * Real.pi * inner ℝ y (δ • ξ)) *
      Complex.I) • Hormander.A.Jc N y := by
    have := Measure.integral_comp_smul (volume : Measure (Carrier N)) f δ
    rw [finrank_euclideanSpace, Fintype.card_fin] at this
    have hpos : (0 : ℝ) < δ ^ N := pow_pos hδ N
    have e : ∫ x, f (δ • x) = ∫ y, Complex.exp (↑(-2 * Real.pi * inner ℝ y (δ • ξ)) *
        Complex.I) • Hormander.A.Jc N y := by
      congr 1; funext y
      simp only [hf, smul_smul, inv_mul_cancel₀ hδ.ne', one_smul, smul_eq_mul,
        inner_smul_left, inner_smul_right]
      simp
    rw [e, abs_of_pos (inv_pos.2 hpos)] at this
    have := congrArg (fun z => (δ ^ N : ℝ) • z) this
    simp only [smul_smul, mul_inv_cancel₀ hpos.ne', one_smul] at this
    exact this.symm
  rw [h1, h2, smul_smul, inv_mul_cancel₀ (pow_pos hδ N).ne', one_smul]

end Hormander.B
