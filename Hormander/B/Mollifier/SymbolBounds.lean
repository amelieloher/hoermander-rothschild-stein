-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import Hormander.B.Mollifier.Symbol
public import Hormander.B.Mollifier.Lipschitz

@[expose] public section

noncomputable section

open MeasureTheory
open scoped FourierTransform SchwartzMap

namespace Hormander.B

variable {N : ℕ}

/-- The complex coordinate function. -/
def coordC (i : Fin N) (x : Carrier N) : ℂ := ((x i : ℝ) : ℂ)

theorem coordC_hasTemperateGrowth (i : Fin N) : (coordC (N := N) i).HasTemperateGrowth := by
  have : coordC (N := N) i = fun x => (Complex.ofRealCLM.comp
      (EuclideanSpace.proj (𝕜 := ℝ) (ι := Fin N) i)) x := rfl
  rw [this]
  exact ContinuousLinearMap.hasTemperateGrowth _

/-- Multiplication by a coordinate on Schwartz functions. -/
def coordMul (i : Fin N) : TestFunction N →L[ℂ] TestFunction N :=
  SchwartzMap.smulLeftCLM ℂ (coordC i)

theorem coordMul_apply (i : Fin N) (φ : TestFunction N) (x : Carrier N) :
    coordMul i φ x = coordC i x * φ x := by
  unfold coordMul
  rw [SchwartzMap.smulLeftCLM_apply_apply (coordC_hasTemperateGrowth i)]
  rfl

theorem norm_mollSymbol_le (δ : ℝ) (hδ : 0 < δ) (ξ : Carrier N) : ‖mollSymbol N δ hδ ξ‖ ≤ 1 :=
  Hormander.A.fourier_Jδ_norm_le_one δ hδ ξ

theorem norm_coordC_le (i : Fin N) (x : Carrier N) : ‖coordC i x‖ ≤ ‖x‖ := by
  simp only [coordC, Complex.norm_real, Real.norm_eq_abs]
  simpa using PiLp.norm_apply_le x i

theorem coordC_smul (i : Fin N) (δ : ℝ) (x : Carrier N) :
    coordC i (δ • x) = (δ : ℂ) * coordC i x := by
  simp [coordC]

theorem coordC_sub (i : Fin N) (x y : Carrier N) :
    coordC i (x - y) = coordC i x - coordC i y := by
  simp [coordC]

/-- Uniform Lipschitz bound for `ξ_i · symbol(ξ)`. -/
theorem mollSymbol_coord_lipschitz (N : ℕ) :
    ∃ L : ℝ, 0 ≤ L ∧ ∀ (δ : ℝ) (hδ : 0 < δ) (i : Fin N) (ξ η : Carrier N),
      ‖coordC i ξ * mollSymbol N δ hδ ξ - coordC i η * mollSymbol N δ hδ η‖ ≤ L * ‖ξ - η‖ := by
  have h : ∀ i : Fin N, ∃ L : ℝ, 0 ≤ L ∧ ∀ x y : Carrier N,
      ‖coordMul i (𝓕 (Hormander.A.Jc N)) x - coordMul i (𝓕 (Hormander.A.Jc N)) y‖ ≤
        L * ‖x - y‖ := fun i => schwartz_lipschitz _
  choose L hL0 hL using h
  refine ⟨∑ i, L i, Finset.sum_nonneg fun i _ => hL0 i, fun δ hδ i ξ η => ?_⟩
  have key : ∀ z : Carrier N, coordC i z * mollSymbol N δ hδ z =
      (δ⁻¹ : ℂ) * coordMul i (𝓕 (Hormander.A.Jc N)) (δ • z) := by
    intro z
    rw [coordMul_apply, mollSymbol_eq, coordC_smul]
    have : (δ : ℂ) ≠ 0 := by exact_mod_cast hδ.ne'
    field_simp
  rw [key ξ, key η, ← mul_sub, norm_mul]
  have h1 := hL i (δ • ξ) (δ • η)
  rw [← smul_sub, norm_smul, Real.norm_eq_abs, abs_of_pos hδ] at h1
  have hnorm : ‖(δ⁻¹ : ℂ)‖ = δ⁻¹ := by
    simp [abs_of_pos hδ]
  rw [hnorm]
  calc δ⁻¹ * ‖coordMul i (𝓕 (Hormander.A.Jc N)) (δ • ξ) - coordMul i (𝓕 (Hormander.A.Jc N)) (δ • η)‖
      ≤ δ⁻¹ * (L i * (δ * ‖ξ - η‖)) := mul_le_mul_of_nonneg_left h1 (by positivity)
    _ = L i * ‖ξ - η‖ := by field_simp
    _ ≤ _ := by
        refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
        exact Finset.single_le_sum (f := L) (fun j _ => hL0 j) (Finset.mem_univ i)

/-- Uniform mixed-difference bound for `ξ_i ξ_k · symbol(ξ)`. -/
theorem mollSymbol_coord2_mixed (N : ℕ) :
    ∃ L : ℝ, 0 ≤ L ∧ ∀ (δ : ℝ) (hδ : 0 < δ) (i k : Fin N) (x d e : Carrier N),
      ‖coordC i (x + d + e) * coordC k (x + d + e) * mollSymbol N δ hδ (x + d + e) -
        coordC i (x + d) * coordC k (x + d) * mollSymbol N δ hδ (x + d) -
        coordC i (x + e) * coordC k (x + e) * mollSymbol N δ hδ (x + e) +
        coordC i x * coordC k x * mollSymbol N δ hδ x‖ ≤ L * (‖d‖ * ‖e‖) := by
  have h : ∀ i k : Fin N, ∃ L : ℝ, 0 ≤ L ∧ ∀ x d e : Carrier N,
      ‖coordMul i (coordMul k (𝓕 (Hormander.A.Jc N))) (x + d + e) -
        coordMul i (coordMul k (𝓕 (Hormander.A.Jc N))) (x + d) -
        coordMul i (coordMul k (𝓕 (Hormander.A.Jc N))) (x + e) +
        coordMul i (coordMul k (𝓕 (Hormander.A.Jc N))) x‖ ≤ L * (‖d‖ * ‖e‖) :=
    fun i k => schwartz_mixed_difference _
  choose L hL0 hL using h
  refine ⟨∑ i, ∑ k, L i k, Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun k _ => hL0 i k,
    fun δ hδ i k x d e => ?_⟩
  have key : ∀ z : Carrier N, coordC i z * coordC k z * mollSymbol N δ hδ z =
      ((δ ^ 2)⁻¹ : ℂ) * coordMul i (coordMul k (𝓕 (Hormander.A.Jc N))) (δ • z) := by
    intro z
    rw [coordMul_apply, coordMul_apply, mollSymbol_eq]
    simp only [coordC_smul]
    have : (δ : ℂ) ≠ 0 := by exact_mod_cast hδ.ne'
    field_simp
  rw [key, key, key, key]
  have hs : ∀ z w : Carrier N, δ • (z + w) = δ • z + δ • w := fun z w => smul_add δ z w
  have h1 := hL i k (δ • x) (δ • d) (δ • e)
  have e1 : δ • (x + d + e) = δ • x + δ • d + δ • e := by rw [hs, hs]
  have e2 : δ • (x + d) = δ • x + δ • d := hs _ _
  have e3 : δ • (x + e) = δ • x + δ • e := hs _ _
  rw [e1, e2, e3]
  set A := coordMul i (coordMul k (𝓕 (Hormander.A.Jc N))) with hA
  have eq : (((δ : ℂ)) ^ 2)⁻¹ * A (δ • x + δ • d + δ • e) -
      (((δ : ℂ)) ^ 2)⁻¹ * A (δ • x + δ • d) - (((δ : ℂ)) ^ 2)⁻¹ * A (δ • x + δ • e) +
      (((δ : ℂ)) ^ 2)⁻¹ * A (δ • x) =
      (((δ : ℂ)) ^ 2)⁻¹ * (A (δ • x + δ • d + δ • e) - A (δ • x + δ • d) -
        A (δ • x + δ • e) + A (δ • x)) := by ring
  rw [eq, norm_mul]
  have hn : ‖(((δ : ℂ)) ^ 2)⁻¹‖ = (δ ^ 2)⁻¹ := by simp [abs_of_pos hδ]
  rw [hn]
  rw [norm_smul, norm_smul, Real.norm_eq_abs, abs_of_pos hδ] at h1
  calc (δ ^ 2)⁻¹ * ‖A (δ • x + δ • d + δ • e) - A (δ • x + δ • d) -
        A (δ • x + δ • e) + A (δ • x)‖
      ≤ (δ ^ 2)⁻¹ * (L i k * (δ * ‖d‖ * (δ * ‖e‖))) :=
        mul_le_mul_of_nonneg_left h1 (by positivity)
    _ = L i k * (‖d‖ * ‖e‖) := by field_simp
    _ ≤ _ := by
        refine mul_le_mul_of_nonneg_right ?_ (by positivity)
        calc L i k ≤ ∑ k', L i k' :=
              Finset.single_le_sum (f := L i) (fun j _ => hL0 i j) (Finset.mem_univ k)
          _ ≤ ∑ i', ∑ k', L i' k' :=
              Finset.single_le_sum (f := fun i' => ∑ k', L i' k')
                (fun j _ => Finset.sum_nonneg fun k' _ => hL0 j k') (Finset.mem_univ i)

end Hormander.B
