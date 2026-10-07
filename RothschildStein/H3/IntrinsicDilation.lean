-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H3.IntrinsicWordTransport
public import RothschildStein.G2.FieldHomogeneity
public import RothschildStein.Definitions.wordWeight

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
open Set TopologicalSpace
namespace RothschildStein.H3
variable {N m : ℕ} (G : HomogeneousGroup N)

/-- Every weighted intrinsic word scales by exactly R to its
fixed word weight, including weight two for the drift (BB p. 339). -/
theorem hasIntrinsicWordDeriv_dilate
    (Ω : Opens (Fin N → ℝ)) (w : Fin m → ℕ+)
    (X : Fin m → (Fin N → ℝ) → (Fin N → ℝ))
    (hX : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (X i))
    (hh : ∀ i, G2.IsHomogeneousField G (X i) ((w i : ℕ) : ℝ))
    {R : ℝ} (hR : 0 < R) (I : List (Fin m))
    {f g : (Fin N → ℝ) → ℝ} (hf : hasIntrinsicWordDeriv X Ω I f g) :
    hasIntrinsicWordDeriv X ⟨G.dilate R ⁻¹' (Ω : Set (Fin N → ℝ)),
      Ω.isOpen.preimage (G2.contDiff_dilate G R).continuous⟩ I
      (f ∘ G.dilate R) (fun x => R ^ (wordWeight w I : ℝ) * g (G.dilate R x)) := by
  have hprod : (I.map (fun i => R ^ ((w i : ℕ) : ℝ))).prod =
      R ^ (wordWeight w I : ℝ) := by
    clear hf
    induction I with
    | nil => simp [wordWeight]
    | cons i I ih =>
      simp only [List.map_cons, List.prod_cons, ih, wordWeight,
        List.sum_cons, Nat.cast_add, Real.rpow_add hR]
  have hd := hasIntrinsicWordDeriv_scaled_pullback Ω (G.dilate R) X X
    (fun i => R ^ ((w i : ℕ) : ℝ))
    (fun i => ne_of_gt (Real.rpow_pos_of_pos hR _)) (G2.contDiff_dilate G R) hX
    (fun i x => by
      rw [(G2.hasFDerivAt_dilate G R x).fderiv, G2.dilationDifferential_apply]
      exact hh i R hR x) I hf
  simpa only [hprod] using hd

end RothschildStein.H3
