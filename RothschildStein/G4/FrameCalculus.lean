-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.G4.Frames
public import Mathlib.LinearAlgebra.Matrix.Nondegenerate

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set Filter
open scoped BigOperators Topology

namespace RothschildStein.G4

/-- Finite sums in the right bracket entry obey linearity when
all right-entry derivatives exist (BB Proposition 9.36, pp. 427–428). -/
theorem bracket_sum_right {n : ℕ} {ι : Type*} [Fintype ι]
    (T : (Fin n → ℝ) → (Fin n → ℝ)) (F : ι → (Fin n → ℝ) → (Fin n → ℝ))
    {x : Fin n → ℝ} (hF : ∀ i, DifferentiableAt ℝ (F i) x) :
    VectorField.lieBracket ℝ T (fun y => ∑ i, F i y) x =
      ∑ i, VectorField.lieBracket ℝ T (F i) x := by
  simp only [VectorField.lieBracket, fderiv_fun_sum (fun i _ => hF i),
    sum_apply, map_sum, Finset.sum_sub_distrib]

/-- Frame coefficients are uniquely determined at a nondegenerate
point (BB Proposition 9.36, p. 428). -/
theorem frame_coefficients_unique {ι : Type*} {n : ℕ}
    {Z : ι → (Fin n → ℝ) → (Fin n → ℝ)} {B : Fin n → ι} {x : Fin n → ℝ}
    (hB : frameDet Z B x ≠ 0) {a b : Fin n → ℝ}
    (heq : (∑ i, a i • Z (B i) x) = ∑ i, b i • Z (B i) x) : a = b := by
  apply Matrix.mulVec_injective_of_det_ne_zero hB
  ext k
  have hk := congrFun heq k
  simpa only [Matrix.mulVec, dotProduct, frameMatrix, Finset.sum_apply,
    Pi.smul_apply, smul_eq_mul, mul_comm] using hk

/-- Differentiating a Cramer coefficient includes the coefficient
Leibniz term. This is the identity used in the weighted generator induction
(BB Proposition 9.36, pp. 427–428). -/
theorem fieldDerivative_frameCoefficient {ι : Type*} {n : ℕ}
    {Ω : Set (Fin n → ℝ)} (hΩ : IsOpen Ω)
    {Z : ι → (Fin n → ℝ) → (Fin n → ℝ)}
    (hZ : ∀ j, ContDiffOn ℝ (⊤ : ℕ∞) (Z j) Ω)
    {V : (Fin n → ℝ) → (Fin n → ℝ)} (hV : ContDiffOn ℝ (⊤ : ℕ∞) V Ω)
    (T : (Fin n → ℝ) → (Fin n → ℝ)) (B : Fin n → ι)
    {x : Fin n → ℝ} (hx : x ∈ Ω) (hB : frameDet Z B x ≠ 0) (i : Fin n) :
    fieldDerivative T (frameCoefficient Z B V i) x =
      frameCoefficient Z B (VectorField.lieBracket ℝ T V) i x -
        ∑ j, frameCoefficient Z B V j x *
          frameCoefficient Z B (VectorField.lieBracket ℝ T (Z (B j))) i x := by
  let a := frameCoefficient Z B V
  let A := fun j => frameCoefficient Z B (VectorField.lieBracket ℝ T (Z (B j)))
  let c := frameCoefficient Z B (VectorField.lieBracket ℝ T V)
  have hnear : Ω ∩ {y | frameDet Z B y ≠ 0} ∈ 𝓝 x := by
    apply inter_mem (hΩ.mem_nhds hx)
    exact ((frameDet_contDiffOn hZ B).contDiffAt (hΩ.mem_nhds hx)).continuousAt.preimage_mem_nhds
      (isOpen_compl_singleton.mem_nhds hB)
  have ha : ∀ j, DifferentiableAt ℝ (a j) x := fun j =>
    ((frameCoefficient_contDiffOn hZ hV B j).contDiffAt hnear).differentiableAt (by simp)
  have hz : ∀ j, DifferentiableAt ℝ (Z (B j)) x := fun j =>
    ((hZ (B j)).contDiffAt (hΩ.mem_nhds hx)).differentiableAt (by simp)
  have he : (fun y => ∑ j, a j y • Z (B j) y) =ᶠ[𝓝 x] V := by
    filter_upwards [hnear] with y hy
    exact (frame_representation Z B V hy.2).symm
  have hb : VectorField.lieBracket ℝ T V x =
      ∑ j, (fieldDerivative T (a j) x • Z (B j) x +
        a j x • VectorField.lieBracket ℝ T (Z (B j)) x) := by
    have hd := he.fderiv_eq (𝕜 := ℝ)
    have hv := he.eq_of_nhds
    have hebr : VectorField.lieBracket ℝ T V x =
        VectorField.lieBracket ℝ T (fun y => ∑ j, a j y • Z (B j) y) x := by
      simp only [VectorField.lieBracket]
      rw [hd, hv]
    rw [hebr]
    rw [bracket_sum_right T (fun j y => a j y • Z (B j) y)
      (fun j => (ha j).smul (hz j))]
    apply Finset.sum_congr rfl
    intro j hj
    exact VectorField.lieBracket_smul_right (ha j) (hz j)
  have heq : (∑ k, c k x • Z (B k) x) =
      ∑ k, (fieldDerivative T (a k) x + ∑ j, a j x * A j k x) • Z (B k) x := by
    rw [← frame_representation Z B (VectorField.lieBracket ℝ T V) hB, hb]
    simp_rw [frame_representation Z B (VectorField.lieBracket ℝ T (Z (B _))) hB]
    simp only [Finset.sum_add_distrib, Finset.smul_sum, smul_smul, add_smul, Finset.sum_smul]
    congr 1
    exact Finset.sum_comm
  have hcoef := congrFun (frame_coefficients_unique hB heq) i
  change c i x = fieldDerivative T (a i) x + ∑ j, a j x * A j i x at hcoef
  dsimp [a, A, c] at hcoef ⊢
  linarith

end RothschildStein.G4
