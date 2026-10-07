-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H3.IntrinsicTransport

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
open Set TopologicalSpace
namespace RothschildStein.H3
variable {N m : ℕ}

/-- intrinsic source gap. Tangent covariance transports every
iterated intrinsic derivative, with one factor for each letter. The proof
uses only the fixed curve definition and imposes no Euclidean smoothness
on the scalar input or intermediate intrinsic derivatives (BB p. 339). -/
theorem hasIntrinsicWordDeriv_scaled_pullback
    (Ω : Opens (Fin N → ℝ)) (φ : (Fin N → ℝ) → (Fin N → ℝ))
    (X Y : Fin m → (Fin N → ℝ) → (Fin N → ℝ))
    (c : Fin m → ℝ) (hc : ∀ i, c i ≠ 0)
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hX : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (X i))
    (hcov : ∀ i x, fderiv ℝ φ x (X i x) = c i • Y i (φ x))
    (I : List (Fin m)) {f g : (Fin N → ℝ) → ℝ}
    (hf : hasIntrinsicWordDeriv Y Ω I f g) :
    hasIntrinsicWordDeriv X ⟨φ ⁻¹' (Ω : Set (Fin N → ℝ)),
      Ω.isOpen.preimage hφ.continuous⟩ I (f ∘ φ)
      (fun x => (I.map c).prod * g (φ x)) := by
  induction I generalizing g with
  | nil =>
    intro x hx
    simpa only [List.map_nil, List.prod_nil, one_mul, Function.comp_apply] using hf hx
  | cons i I ih =>
    obtain ⟨h, hI, hi⟩ := hf
    have hd := hasIntrinsicDeriv_const_mul _ (X i)
      (hasIntrinsicDeriv_scaled_pullback Ω φ (X i) (Y i) (hc i) hφ (hX i)
        (hcov i) hi) (I.map c).prod
    refine ⟨fun x => (I.map c).prod * h (φ x), ih hI, ?_⟩
    simpa only [List.map_cons, List.prod_cons, Function.comp_apply,
      mul_left_comm (I.map c).prod (c i), mul_assoc] using hd

end RothschildStein.H3
