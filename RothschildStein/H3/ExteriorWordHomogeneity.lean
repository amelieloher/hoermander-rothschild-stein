-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H3.ExteriorKernelScaling
public import RothschildStein.H3.WordHomogeneity
public import RothschildStein.H1.PuncturedFieldHomogeneity

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public section
noncomputable section
open Set
namespace RothschildStein.H3
variable {N m : ℕ} {G : HomogeneousGroup N}

/-- far part. Arbitrary ordered words in homogeneous smooth
fields lower the degree of a punctured smooth kernel by their weight.
This includes mixed left/right words needed on BB p. 383. -/
theorem homogeneous_word_kernel (w : Fin m → ℕ+)
    (Y : Fin m → (Fin N → ℝ) → (Fin N → ℝ))
    (hs : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (Y i))
    (hh : ∀ i, G2.IsHomogeneousField G (Y i) ((w i : ℕ) : ℝ))
    {F : (Fin N → ℝ) → ℝ} (hF : ContDiffOn ℝ (⊤ : ℕ∞) F {0}ᶜ)
    {γ : ℝ} (hhom : ∀ t : ℝ, 0 < t → ∀ x, x ≠ 0 → F (G.dilate t x) = t ^ γ * F x)
    (I : List (Fin m)) :
    ContDiffOn ℝ (⊤ : ℕ∞) (wordDerivative Y I F) {0}ᶜ ∧
    ∀ t : ℝ, 0 < t → ∀ x, x ≠ 0 →
      wordDerivative Y I F (G.dilate t x) =
        t ^ (γ - (wordWeight w I : ℝ)) * wordDerivative Y I F x := by
  refine ⟨S.contDiffOn_wordDerivative ⟨{0}ᶜ, isOpen_compl_singleton⟩ Y
    (fun i => (hs i).contDiffOn) I F hF, ?_⟩
  induction I with
  | nil => simpa only [wordDerivative, wordWeight, List.map_nil, List.sum_nil,
      Nat.cast_zero, sub_zero] using hhom
  | cons i I ih =>
    have htail := S.contDiffOn_wordDerivative ⟨{0}ᶜ, isOpen_compl_singleton⟩ Y
      (fun j => (hs j).contDiffOn) I F hF
    intro t ht x hx
    have hd := H1.fieldDerivative_punctured_homogeneity G (hh i)
      (htail.of_le (by simp)) ih ht hx
    have he : γ - (wordWeight w (i :: I) : ℝ) =
        γ - (wordWeight w I : ℝ) - ((w i : ℕ) : ℝ) := by
      simp only [wordWeight, List.map_cons, List.sum_cons, Nat.cast_add]
      ring
    simpa only [wordDerivative, he] using hd

/-- Word differentiation commutes with scalar multiplication
for arbitrary scalar inputs, including at points lacking derivatives. -/
theorem wordDerivative_const_mul
    (Y : Fin m → (Fin N → ℝ) → (Fin N → ℝ)) (I : List (Fin m))
    (c : ℝ) (F : (Fin N → ℝ) → ℝ) :
    wordDerivative Y I (fun x => c * F x) = fun x => c * wordDerivative Y I F x := by
  induction I with
  | nil => rfl
  | cons i I ih =>
    simp only [wordDerivative, ih]
    funext x
    unfold fieldDerivative
    change fderiv ℝ (c • wordDerivative Y I F) x (Y i x) = _
    rw [fderiv_const_smul_field]
    rfl

/-- The exterior cutoff word has exactly the expected inverse
scale factor, without constructing a second operator calculus. -/
theorem exteriorCutoffKernel_word_scale (w : Fin m → ℕ+)
    (Y : Fin m → (Fin N → ℝ) → (Fin N → ℝ))
    (hsY : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (Y i))
    (hhY : ∀ i, G2.IsHomogeneousField G (Y i) ((w i : ℕ) : ℝ))
    {ν F : (Fin N → ℝ) → ℝ} (hν : G.IsHomogeneousGauge ν)
    (hsν : ContDiffOn ℝ (⊤ : ℕ∞) ν {0}ᶜ)
    {φ : ℝ → ℝ} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hone : ∀ t : ℝ, t ≤ 1 / 2 → φ t = 1)
    (hF : ContDiffOn ℝ (⊤ : ℕ∞) F {0}ᶜ) {γ : ℝ}
    (hhom : ∀ t : ℝ, 0 < t → ∀ x, x ≠ 0 → F (G.dilate t x) = t ^ γ * F x)
    (I : List (Fin m)) {ε : ℝ} (hε : 0 < ε) (x : Fin N → ℝ) :
    wordDerivative Y I (exteriorCutoffKernel ν φ F ε) x =
      ε ^ (γ - (wordWeight w I : ℝ)) *
        wordDerivative Y I (exteriorCutoffKernel ν φ F 1) (G.dilate ε⁻¹ x) := by
  have hc := contDiff_kernel_exterior_cutoff hν hsν hφ hone hF zero_lt_one
  rw [exteriorCutoffKernel_scale hν hone hhom hε, wordDerivative_const_mul]
  change ε ^ γ * wordDerivative Y I (exteriorCutoffKernel ν φ F 1 ∘ G.dilate ε⁻¹) x = _
  rw [wordDerivative_cutoff_dilation w Y hsY hhY I
      (χ := exteriorCutoffKernel ν φ F 1) hc hε,
    ← mul_assoc, ← Real.rpow_add hε]
  congr 2

end RothschildStein.H3
