-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.G2.InversePolynomial
public import Mathlib.MeasureTheory.Integral.Bochner.Basic

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false

@[expose] public section
noncomputable section
namespace RothschildStein.G2
open MeasureTheory Function
variable {N : ℕ} (G : HomogeneousGroup N)

/-- Left translation is triangular unipotent (BB Theorem 3.6(b), p. 96). -/
theorem leftTranslation_isTriangular (y : Fin N → ℝ) :
    IsTriangular (G.mul y) (fun _ => 1) := by
  intro k x x' hxx'
  rw [mul_coordinate, mul_coordinate, correction_eval_congr G k (fun _ _ => rfl) hxx']
  ring

/-- Right translation is triangular unipotent (BB Theorem 3.6(b), p. 96). -/
theorem rightTranslation_isTriangular (y : Fin N → ℝ) :
    IsTriangular (fun x => G.mul x y) (fun _ => 1) := by
  intro k x x' hxx'
  change G.mul x y k - 1 * x k = G.mul x' y k - 1 * x' k
  rw [mul_coordinate, mul_coordinate, correction_eval_congr G k hxx' (fun _ _ => rfl)]
  ring

/-- Left translations preserve Lebesgue measure (BB Theorem 3.6(d), p. 96). -/
theorem measurePreserving_leftTranslation (y : Fin N → ℝ) : MeasurePreserving (G.mul y) :=
  (triangular_measurePreserving_bijective _ _
    ((continuous_mul G).comp (continuous_const.prodMk continuous_id)).measurable
    (fun _ => Or.inl rfl) (leftTranslation_isTriangular G y)).1

/-- Right translations preserve Lebesgue measure (BB Theorem 3.6(d), p. 96). -/
theorem measurePreserving_rightTranslation (y : Fin N → ℝ) :
    MeasurePreserving (fun x => G.mul x y) :=
  (triangular_measurePreserving_bijective _ _
    ((continuous_mul G).comp (continuous_id.prodMk continuous_const)).measurable
    (fun _ => Or.inl rfl) (rightTranslation_isTriangular G y)).1

/-- Polynomial inversion preserves Lebesgue measure (BB Proposition 3.7, p. 98). -/
theorem measurePreserving_inv : MeasurePreserving G.inv :=
  (triangular_measurePreserving_bijective _ _ (continuous_inv G).measurable
    (fun _ => Or.inr rfl) (inv_isTriangular G)).1

/-- Left translation is bijective (BB Theorem 3.6(d), p. 96). -/
theorem leftTranslation_bijective (y : Fin N → ℝ) : Bijective (G.mul y) :=
  (triangular_measurePreserving_bijective _ _
    (measurePreserving_leftTranslation G y).measurable
    (fun _ => Or.inl rfl) (leftTranslation_isTriangular G y)).2

/-- Right translation is bijective (BB Theorem 3.6(d), p. 96). -/
theorem rightTranslation_bijective (y : Fin N → ℝ) : Bijective (fun x => G.mul x y) :=
  (triangular_measurePreserving_bijective _ _
    (measurePreserving_rightTranslation G y).measurable
    (fun _ => Or.inl rfl) (rightTranslation_isTriangular G y)).2

/-- Inversion is a bijection (BB Proposition 3.7, p. 98). -/
theorem inv_bijective : Bijective G.inv :=
  ⟨(Function.LeftInverse.injective (inv_inv G)), Function.RightInverse.surjective (inv_inv G)⟩

/-- Inverse left-product Fubini substitution (BB p. 96). -/
theorem measurePreserving_invLeftSkew :
    MeasurePreserving (fun p : (Fin N → ℝ) × (Fin N → ℝ) => (p.1, G.mul (G.inv p.1) p.2)) := by
  rw [Measure.volume_eq_prod]
  exact (MeasurePreserving.id _).skew_product (g := fun y x => G.mul (G.inv y) x)
    ((continuous_mul G).comp (((continuous_inv G).comp continuous_fst).prodMk continuous_snd)).measurable
    (Filter.Eventually.of_forall fun y => (measurePreserving_leftTranslation G (G.inv y)).map_eq)

/-- Bochner integral substitution under left translation (BB Theorem 3.6(d), p. 96). -/
theorem integral_leftTranslation {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (y : Fin N → ℝ) (f : (Fin N → ℝ) → E) : ∫ x, f (G.mul y x) = ∫ x, f x :=
  (measurePreserving_leftTranslation G y).integral_comp
    ((measurePreserving_leftTranslation G y).measurable.measurableEmbedding
      (leftTranslation_bijective G y).injective) f

end RothschildStein.G2
