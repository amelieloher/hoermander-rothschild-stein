-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H3.RadialWordTerms
public import RothschildStein.S.Transposes
public import RothschildStein.S.ClassicalWords

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public section
noncomputable section
namespace RothschildStein.H3
open Set
open scoped Topology

/-- The ordered product of gauge-word factors in one radial expansion term. -/
def radialGaugeProduct {n m : ℕ}
    (X : Fin m → (Fin n → ℝ) → (Fin n → ℝ)) (ν : (Fin n → ℝ) → ℝ) :
    List (List (Fin m)) → (Fin n → ℝ) → ℝ
  | [], _ => 1
  | K :: Ks, x => wordDerivative X K ν x * radialGaugeProduct X ν Ks x

/-- Every gauge-factor product is smooth on the punctured domain. -/
theorem radialGaugeProduct_contDiffOn {n m : ℕ}
    (X : Fin m → (Fin n → ℝ) → (Fin n → ℝ))
    (hX : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (X i)) {ν : (Fin n → ℝ) → ℝ}
    (hν : ContDiffOn ℝ (⊤ : ℕ∞) ν {0}ᶜ) (Ks : List (List (Fin m))) :
    ContDiffOn ℝ (⊤ : ℕ∞) (radialGaugeProduct X ν Ks) {0}ᶜ := by
  induction Ks with
  | nil => exact contDiffOn_const
  | cons K Ks ih =>
    exact (RothschildStein.S.contDiffOn_wordDerivative ⟨{0}ᶜ,isOpen_compl_singleton⟩ X
      (fun i => (hX i).contDiffOn) K ν hν).mul ih

/-- Differentiating the ordered product differentiates each
 gauge factor once, retaining all multiplicities. -/
theorem fieldDerivative_radialGaugeProduct {n m : ℕ}
    (X : Fin m → (Fin n → ℝ) → (Fin n → ℝ))
    (hX : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (X i)) {ν : (Fin n → ℝ) → ℝ}
    (hν : ContDiffOn ℝ (⊤ : ℕ∞) ν {0}ᶜ)
    (i : Fin m) (Ks : List (List (Fin m))) {x : Fin n → ℝ} (hx : x ≠ 0) :
    fieldDerivative (X i) (radialGaugeProduct X ν Ks) x =
      ((radialFactorDerivatives i Ks).map (fun Ls => radialGaugeProduct X ν Ls x)).sum := by
  induction Ks with
  | nil => simp [radialGaugeProduct,radialFactorDerivatives,fieldDerivative]
  | cons K Ks ih =>
    have hdK : DifferentiableAt ℝ (wordDerivative X K ν) x :=
      ((RothschildStein.S.contDiffOn_wordDerivative ⟨{0}ᶜ,isOpen_compl_singleton⟩ X
        (fun i => (hX i).contDiffOn) K ν hν).contDiffAt
        (isOpen_compl_singleton.mem_nhds hx)).differentiableAt (by simp)
    have hdKs : DifferentiableAt ℝ (radialGaugeProduct X ν Ks) x :=
      ((radialGaugeProduct_contDiffOn X hX hν Ks).contDiffAt
        (isOpen_compl_singleton.mem_nhds hx)).differentiableAt (by simp)
    change fieldDerivative (X i) (fun y => wordDerivative X K ν y * radialGaugeProduct X ν Ks y) x = _
    rw [RothschildStein.S.fieldDerivative_mul (X i) _ _ x hdK hdKs,ih]
    simp only [radialFactorDerivatives,List.map_cons,List.sum_cons,List.map_map,
      Function.comp_def,radialGaugeProduct,wordDerivative,List.sum_map_mul_left]

end RothschildStein.H3
