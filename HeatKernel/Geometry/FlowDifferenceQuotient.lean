-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Geometry.HorizontalFlow

/-! Haar substitution and the bounded difference quotients of horizontal Lipschitz functions. -/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set MeasureTheory RothschildStein
open scoped BigOperators NNReal ENNReal
namespace HeatKernel

/-- Haar invariance transfers the horizontal difference quotient from a function to its test. -/
theorem integral_horizontalFlow_differenceQuotient {N q : ℕ} (G : HomogeneousGroup N)
    (hq : q ≤ N) (b : Fin q → ℝ) (h : ℝ) (φ ψ : (Fin N → ℝ) → ℝ)
    (hf : Integrable (fun x => φ (horizontalFlow G hq b x h) * ψ x))
    (hg : Integrable (fun x => φ x * ψ x)) :
    (∫ x, φ x * (ψ (horizontalFlow G hq b x (-h)) - ψ x) / h) =
      ∫ x, ((φ (horizontalFlow G hq b x h) - φ x) / h) * ψ x := by
  have hf' : Integrable (fun x => φ x * ψ (horizontalFlow G hq b x (-h))) := by
    have hp := (measurePreserving_horizontalFlow G hq b (-h)).integrable_comp_of_integrable hf
    simpa only [Function.comp_def, ← horizontalFlow_add, neg_add_cancel, horizontalFlow_zero] using hp
  have hs := integral_horizontalFlow G hq b (-h) (fun x => φ (horizontalFlow G hq b x h) * ψ x)
  simp only [← horizontalFlow_add, neg_add_cancel, horizontalFlow_zero] at hs
  have he₁ : (fun x => φ x * (ψ (horizontalFlow G hq b x (-h)) - ψ x) / h) =
      fun x => (φ x * ψ (horizontalFlow G hq b x (-h)) - φ x * ψ x) / h := by
    funext x
    ring
  have he₂ : (fun x => ((φ (horizontalFlow G hq b x h) - φ x) / h) * ψ x) =
      fun x => (φ (horizontalFlow G hq b x h) * ψ x - φ x * ψ x) / h := by
    funext x
    ring
  rw [he₁, he₂, integral_div, integral_div, integral_sub hf' hg, integral_sub hf hg, hs]

/-- Horizontal Lipschitz functions have uniformly bounded constant-control difference quotients. -/
theorem abs_horizontalFlow_differenceQuotient_le {N q : ℕ} (G : HomogeneousGroup N)
    (hq : q ≤ N) (b : Fin q → ℝ) (L : ℝ≥0) (φ : (Fin N → ℝ) → ℝ)
    (hφ : ∀ x y, edist (φ x) (φ y) ≤ (L : ℝ≥0∞) * horizontalL2Distance (G.horizontalFields hq) x y)
    (x : Fin N → ℝ) {h : ℝ} (hh : h ≠ 0) :
    |(φ (horizontalFlow G hq b x h) - φ x) / h| ≤ L * Real.sqrt (∑ i, b i ^ 2) := by
  have hd := horizontalL2Distance_horizontalFlow_le G hq b x 0 h
  simp only [horizontalFlow_zero, sub_zero] at hd
  have he := (hφ x (horizontalFlow G hq b x h)).trans
    (mul_le_mul le_rfl hd bot_le bot_le)
  have hc : (L : ℝ≥0∞) * ENNReal.ofReal (|h| * Real.sqrt (∑ i, b i ^ 2)) =
      ENNReal.ofReal ((L : ℝ) * (|h| * Real.sqrt (∑ i, b i ^ 2))) := by
    rw [ENNReal.ofReal_mul L.coe_nonneg, ENNReal.ofReal_coe_nnreal]
  rw [hc, edist_dist] at he
  have hr : dist (φ x) (φ (horizontalFlow G hq b x h)) ≤
      (L : ℝ) * (|h| * Real.sqrt (∑ i, b i ^ 2)) :=
    (ENNReal.ofReal_le_ofReal_iff (by positivity)).1 he
  rw [Real.dist_eq, abs_sub_comm] at hr
  rw [abs_div, div_le_iff₀ (abs_pos.mpr hh)]
  nlinarith only [hr]

end HeatKernel
