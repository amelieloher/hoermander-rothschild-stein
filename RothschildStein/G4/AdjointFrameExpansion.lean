-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.G4.ControlAdjointExpansion
public import RothschildStein.G4.BracketReduction

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set
open scoped BigOperators

namespace RothschildStein.G4

/-- Cramer coefficients distribute over a finite vector-field
combination even when its carrier differs from the frame carrier. -/
theorem frameCoefficient_external_linear_combination {ι σ : Type*} [Fintype ι] {n : ℕ}
    (Z : σ → (Fin n → ℝ) → (Fin n → ℝ)) (B : Fin n → σ)
    (V : (Fin n → ℝ) → (Fin n → ℝ))
    (Y : ι → (Fin n → ℝ) → (Fin n → ℝ)) (c : ι → ℝ)
    (i : Fin n) (x : Fin n → ℝ) (heq : V x = ∑ j, c j • Y j x) :
    frameCoefficient Z B V i x = ∑ j, c j * frameCoefficient Z B (Y j) i x := by
  unfold frameCoefficient
  change (Matrix.cramer (frameMatrix Z B x) (V x)) i / frameDet Z B x = _
  rw [heq, map_sum]
  simp only [map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Matrix.cramer_apply]
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro j hj
  unfold replacementDet
  ring

/-- Frame coordinates of the actual constant-control adjoint have
an exact ordered-bracket expansion (BB Lemma 9.48, pp. 441–443). -/
theorem adjoint_constantControl_frameCoefficient_expansion
    {ι σ : Type*} [Fintype ι] {n : ℕ} {Ω : Set (Fin n → ℝ)} (hΩ : IsOpen Ω)
    {W : ι → (Fin n → ℝ) → (Fin n → ℝ)}
    (hW : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (W i) Ω) (a : ι → ℝ)
    {Y : (Fin n → ℝ) → (Fin n → ℝ)} (hY : ContDiffOn ℝ (⊤ : ℕ∞) Y Ω)
    (Z : σ → (Fin n → ℝ) → (Fin n → ℝ)) (B : Fin n → σ)
    (j : ℕ) (i : Fin n) {x : Fin n → ℝ} (hx : x ∈ Ω) :
    frameCoefficient Z B
      ((VectorField.lieBracket ℝ (fun y => ∑ k, a k • W k y))^[j] Y) i x =
      ∑ L : Fin j → ι, (∏ k, a (L k)) *
        frameCoefficient Z B (orderedAdjoints W (List.ofFn L) Y) i x :=
  frameCoefficient_external_linear_combination Z B _ _ _ i x
    (adjoint_constantControl_expansion hΩ hW a hY j hx)

end RothschildStein.G4
