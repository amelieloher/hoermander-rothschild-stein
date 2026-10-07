-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module
public import RothschildStein.G3.Grading
public import RothschildStein.G3.DilationSpan
@[expose] public section
noncomputable section
open scoped BigOperators
namespace RothschildStein.G3

/-- Weighted projections are orthogonal idempotents
(BB Proposition 10.42, pp. 523–525). -/
theorem weightProjection_comp {a s : ℕ} {p : Fin a → ℕ+} (k l : ℕ)
    (f : WordCoefficients a s p) :
    weightProjection k (weightProjection l f) = if k = l then weightProjection k f else 0 := by
  by_cases hkl : k = l
  · subst l
    rw [ite_eq_left rfl]
    funext J
    change (if wordWeight p J.val = k then
      (if wordWeight p J.val = k then f J else 0) else 0) =
      (if wordWeight p J.val = k then f J else 0)
    by_cases hk : wordWeight p J.val = k <;> simp [hk]
  · rw [ite_eq_right hkl]
    funext J
    change (if wordWeight p J.val = k then
      (if wordWeight p J.val = l then f J else 0) else 0) = 0
    by_cases hk : wordWeight p J.val = k <;>
      by_cases hl : wordWeight p J.val = l <;> simp_all

/-- A homogeneous finite coefficient vector has homogeneous zero extension
(BB Proposition 10.42, p. 523). -/
theorem homogeneous_extend_of_projection {a s : ℕ} {p : Fin a → ℕ+} {k : ℕ}
    {f : WordCoefficients a s p} (hf : weightProjection k f = f) :
    Homogeneous p k (extend f) := by
  intro J hJ
  unfold extend
  split
  · rename_i hw
    have h := congrFun hf (boundedWord p J hw)
    change (if wordWeight p J = k then f _ else 0) = f _ at h
    rw [ite_eq_right hJ] at h
    exact h.symm
  · rfl

/-- Multiplication of finite homogeneous layers adds weights
(BB Proposition 10.42, p. 523). -/
theorem weightProjection_product {a s : ℕ} {p : Fin a → ℕ+} {k l : ℕ}
    {f g : WordCoefficients a s p} (hf : weightProjection k f = f)
    (hg : weightProjection l g = g) :
    weightProjection (k + l) (truncatedProduct f g) = truncatedProduct f g := by
  have hc := homogeneous_convolution p (homogeneous_extend_of_projection hf)
    (homogeneous_extend_of_projection hg)
  funext J
  change (if wordWeight p J.val = k + l then
    wordConvolution (extend f) (extend g) J.val else 0) =
      wordConvolution (extend f) (extend g) J.val
  by_cases hJ : wordWeight p J.val = k + l
  · exact ite_eq_left hJ
  · rw [ite_eq_right hJ, hc J.val hJ]

/-- Weighted dilation acts by its weight power on each homogeneous layer
(BB Proposition 10.48, p. 526). -/
theorem finiteDilate_of_projection {a s : ℕ} {p : Fin a → ℕ+} {k : ℕ}
    {f : WordCoefficients a s p} (hf : weightProjection k f = f) (t : ℝ) :
    finiteDilate t f = t ^ k • f := by
  funext J
  have h := congrFun hf J
  change (if wordWeight p J.val = k then f J else 0) = f J at h
  change t ^ wordWeight p J.val * f J = t ^ k * f J
  by_cases hJ : wordWeight p J.val = k
  · rw [hJ]
  · rw [ite_eq_right hJ] at h
    rw [← h, mul_zero, mul_zero]
end RothschildStein.G3
