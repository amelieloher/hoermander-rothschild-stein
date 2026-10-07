-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.G1.BracketAlgebra
public import Mathlib.LinearAlgebra.Matrix.Adjugate

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set
open scoped BigOperators

namespace RothschildStein.G4

variable {ι : Type*} {n : ℕ}

/-- Matrices use field values as columns. -/
def frameMatrix (Z : ι → (Fin n → ℝ) → (Fin n → ℝ))
    (B : Fin n → ι) (x : Fin n → ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  fun k j => Z (B j) x k

/-- The frame determinant `λ_B`. -/
def frameDet (Z : ι → (Fin n → ℝ) → (Fin n → ℝ))
    (B : Fin n → ι) (x : Fin n → ℝ) : ℝ := (frameMatrix Z B x).det

/-- The determinant replacing column `i` by an arbitrary vector. -/
def replacementDet (Z : ι → (Fin n → ℝ) → (Fin n → ℝ))
    (B : Fin n → ι) (v : Fin n → ℝ) (i : Fin n) (x : Fin n → ℝ) : ℝ :=
  ((frameMatrix Z B x).updateCol i v).det

/-- Cramer coefficients on the nondegenerate frame domain. -/
def frameCoefficient (Z : ι → (Fin n → ℝ) → (Fin n → ℝ))
    (B : Fin n → ι) (V : (Fin n → ℝ) → (Fin n → ℝ))
    (i : Fin n) (x : Fin n → ℝ) : ℝ :=
  replacementDet Z B (V x) i x / frameDet Z B x

/-- Adjugate identity remains valid at singular frames
(BB Proposition 9.29, p. 422). -/
theorem frame_adjugate_identity (Z : ι → (Fin n → ℝ) → (Fin n → ℝ))
    (B : Fin n → ι) (v : Fin n → ℝ) (x : Fin n → ℝ) :
    frameDet Z B x • v = ∑ i, replacementDet Z B v i x • Z (B i) x := by
  have h := Matrix.mulVec_cramer (frameMatrix Z B x) v
  ext k
  have hk := congrFun h k
  simpa only [frameDet, frameMatrix, Matrix.mulVec, dotProduct, Matrix.cramer_apply,
    replacementDet, Pi.smul_apply, smul_eq_mul, Finset.sum_apply, mul_comm] using hk.symm

/-- Cramer's formula gives the actual vector representation
(BB Proposition 9.29, pp. 421–422). -/
theorem frame_representation (Z : ι → (Fin n → ℝ) → (Fin n → ℝ))
    (B : Fin n → ι) (V : (Fin n → ℝ) → (Fin n → ℝ))
    {x : Fin n → ℝ} (hB : frameDet Z B x ≠ 0) :
    V x = ∑ i, frameCoefficient Z B V i x • Z (B i) x := by
  have h := congrArg (fun v : Fin n → ℝ => (frameDet Z B x)⁻¹ • v)
    (frame_adjugate_identity Z B (V x) x)
  simpa only [smul_smul, inv_mul_cancel₀ hB, one_smul, Finset.smul_sum,
    frameCoefficient, div_eq_mul_inv, mul_comm] using h

/-- Replacing column `i` by a short field is exactly the determinant
of the corresponding replaced word frame (BB p. 422). -/
theorem replacementDet_eq_update (Z : ι → (Fin n → ℝ) → (Fin n → ℝ))
    (B : Fin n → ι) (J : ι) (i : Fin n) (x : Fin n → ℝ) :
    replacementDet Z B (Z J x) i x = frameDet Z (Function.update B i J) x := by
  classical
  unfold replacementDet frameDet
  congr 1
  ext k j
  by_cases hj : j = i
  · subst j
    simp [frameMatrix]
  · simp [frameMatrix, hj]

/-- Smoothness of determinants on the original open domain
(BB Proposition 9.29, p. 422). -/
theorem frameDet_contDiffOn {Ω : Set (Fin n → ℝ)}
    {Z : ι → (Fin n → ℝ) → (Fin n → ℝ)}
    (hZ : ∀ j, ContDiffOn ℝ (⊤ : ℕ∞) (Z j) Ω) (B : Fin n → ι) :
    ContDiffOn ℝ (⊤ : ℕ∞) (frameDet Z B) Ω := by
  classical
  unfold frameDet
  simp only [Matrix.det_apply']
  apply ContDiffOn.sum
  intro σ hσ
  apply contDiffOn_const.mul
  apply contDiffOn_prod
  intro j hj
  exact (contDiffOn_pi.mp (hZ (B j))) (σ j)

/-- Smooth replacement numerators (BB Proposition 9.29, p. 422). -/
theorem replacementDet_contDiffOn {Ω : Set (Fin n → ℝ)}
    {Z : ι → (Fin n → ℝ) → (Fin n → ℝ)}
    (hZ : ∀ j, ContDiffOn ℝ (⊤ : ℕ∞) (Z j) Ω)
    {V : (Fin n → ℝ) → (Fin n → ℝ)} (hV : ContDiffOn ℝ (⊤ : ℕ∞) V Ω)
    (B : Fin n → ι) (i : Fin n) :
    ContDiffOn ℝ (⊤ : ℕ∞) (fun x => replacementDet Z B (V x) i x) Ω := by
  classical
  unfold replacementDet
  simp only [Matrix.det_apply']
  apply ContDiffOn.sum
  intro σ hσ
  apply contDiffOn_const.mul
  apply contDiffOn_prod
  intro j hj
  by_cases hji : j = i
  · subst j
    simpa [Matrix.updateCol_apply] using (contDiffOn_pi.mp hV) (σ i)
  · simpa [Matrix.updateCol_apply, hji, frameMatrix] using (contDiffOn_pi.mp (hZ (B j))) (σ j)

/-- The frame coefficients are smooth wherever the determinant
is nonzero, without a bound near a degenerating frame (BB p. 422). -/
theorem frameCoefficient_contDiffOn {Ω : Set (Fin n → ℝ)}
    {Z : ι → (Fin n → ℝ) → (Fin n → ℝ)}
    (hZ : ∀ j, ContDiffOn ℝ (⊤ : ℕ∞) (Z j) Ω)
    {V : (Fin n → ℝ) → (Fin n → ℝ)} (hV : ContDiffOn ℝ (⊤ : ℕ∞) V Ω)
    (B : Fin n → ι) (i : Fin n) :
    ContDiffOn ℝ (⊤ : ℕ∞) (frameCoefficient Z B V i)
      (Ω ∩ {x | frameDet Z B x ≠ 0}) := by
  exact ((replacementDet_contDiffOn hZ hV B i).mono inter_subset_left).div
    ((frameDet_contDiffOn hZ B).mono inter_subset_left) (fun x hx => hx.2)

end RothschildStein.G4
