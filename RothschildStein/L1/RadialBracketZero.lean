-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module
public import RothschildStein.L1.RadialSecondJets
@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set TopologicalSpace
namespace RothschildStein.L1

/-- The degree-zero bracket identity starts the radial weight induction
without referring to a negative ordinary jet order. -/
theorem radial_frame_bracket_zero {N : ℕ} (Ω : Opens (Fin N → ℝ))
    (h0 : (0 : Fin N → ℝ) ∈ Ω) (Z : Fin N → (Fin N → ℝ) → (Fin N → ℝ))
    (hZ : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (Z i) Ω)
    (hrad : ∀ u ∈ Ω, ∑ i, u i • Z i u = u)
    (hZ0 : ∀ i, Z i 0 = Pi.single i 1) (i j : Fin N) :
    VectorField.lieBracket ℝ (Z i) (Z j) 0 =
      (2 : ℝ) • VectorField.lieBracket ℝ (Z i) (fun _ => Pi.single j 1) 0 := by
  have ha := radial_frame_first_fderiv_antisymmetry Ω h0 Z hZ hrad i j
  have he : fderiv ℝ (Z i) 0 (Pi.single j 1) =
      -fderiv ℝ (Z j) 0 (Pi.single i 1) := by
    calc
      _ = fderiv ℝ (Z i) 0 (Pi.single j 1) + 0 := (add_zero _).symm
      _ = fderiv ℝ (Z i) 0 (Pi.single j 1) +
          -(fderiv ℝ (Z i) 0 (Pi.single j 1) + fderiv ℝ (Z j) 0 (Pi.single i 1)) := by
        rw [ha, neg_zero]
      _ = _ := by abel
  simp only [VectorField.lieBracket, hZ0, fderiv_const_apply, zero_apply, zero_sub]
  rw [he]
  simp only [neg_neg, sub_eq_add_neg, two_smul]
end RothschildStein.L1
