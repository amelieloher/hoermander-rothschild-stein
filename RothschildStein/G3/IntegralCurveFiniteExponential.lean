-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module
public import RothschildStein.G3.LinearInputExponentialTail
public import RothschildStein.G3.FlowTaylorJetBounds
@[expose] public section
noncomputable section
open Set TopologicalSpace
open scoped BigOperators
namespace RothschildStein.G3

/-- The actual time-one flow of a weighted constant field input is
approximated by its weighted finite exponential operator. The error uses
an explicit finite polynomial in field/function jets and tail coefficients
(BB Lemma 9.22, pp. 413–414). -/
theorem integralCurve_linearInput_finiteExponential_bound {a s Q N R : ℕ}
    (p : Fin a → ℕ+) (Ω : Opens (Fin N → ℝ))
    (X : Fin a → (Fin N → ℝ) → (Fin N → ℝ))
    (hX : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (X i) Ω)
    (hq : ∀ i, (p i : ℕ) ≤ Q) (δ : ℝ) (c : Fin a → ℝ)
    (V : (Fin N → ℝ) → (Fin N → ℝ))
    (hV : ContDiffOn ℝ (⊤ : ℕ∞) V Ω)
    (hcomb : V = fun x => ∑ i, c i • (δ ^ (p i : ℕ) • X i x))
    {a₀ b₀ Bv Bx F : ℝ} (α : ℝ → (Fin N → ℝ))
    (hODE : ∀ t ∈ Ioo a₀ b₀, HasDerivAt α (V (α t)) t)
    (hmem : ∀ t ∈ Ioo a₀ b₀, α t ∈ Ω)
    (hsegment : ∀ t ∈ Icc (0 : ℝ) 1, t ∈ Ioo a₀ b₀)
    (f : smoothOnFunctions Ω) (hn : s + 1 ≤ R) (hBx : 0 ≤ Bx)
    (hVjet : ∀ t ∈ Icc (0 : ℝ) 1, ∀ j ≤ R,
      ‖iteratedFDeriv ℝ j V (α t)‖ ≤ |δ| * Bv)
    (hXjet : ∀ i, ∀ j ≤ s, ‖iteratedFDeriv ℝ j (X i) (α 0)‖ ≤ Bx)
    (hfjet : ∀ t ∈ Icc (0 : ℝ) 1, ∀ j ≤ R,
      ‖iteratedFDeriv ℝ j f.val (α t)‖ ≤ F) (hδ : |δ| ≤ 1) :
    ‖f.val (α 1) -
      (differentialWordEvaluation Ω (fun i => δ ^ (p i : ℕ) • X i)
        (fun i => ((hX i).const_smul (δ ^ (p i : ℕ))).congr (fun x _ => by ext j; rfl))
        (finitePolynomial (finiteExp (truncateSeries (s := s) (p := p)
          (polynomialSeries a (linearWordPolynomial c))))) f).val (α 0)‖ ≤
      (((2 ^ R * Bv) ^ (s + 1) * F) +
        exponentialTailCoefficientBound s Q p (linearWordPolynomial c) Bx F) * |δ| ^ (s + 1) := by
  let Y := fun i => δ ^ (p i : ℕ) • X i
  have hY : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (Y i) Ω :=
    fun i => ((hX i).const_smul (δ ^ (p i : ℕ))).congr (fun x _ => by ext j; rfl)
  have hx : α 0 ∈ Ω := hmem 0 (hsegment 0 (by simp))
  have hop : differentialWordEvaluation Ω Y hY (linearWordPolynomial c) =
      smoothFieldOperator Ω V hV := by
    subst V
    exact differentialWordEvaluation_linearWordPolynomial Ω Y hY c
  have he := differentialWordEvaluation_wordPolynomialExp_eq_fieldPowers Ω Y hY
    (linearWordPolynomial c) V hV hop s f hx
  have ht := integralCurve_pullback_taylor_bound_of_jet_bounds (R := R) Ω V hV α hODE hmem
    f.val f.property s hn (t := 1) (by simpa only [mul_one] using hsegment)
    (by simpa only [mul_one] using hVjet) (by simpa only [mul_one] using hfjet)
  simp only [one_pow, one_div, abs_one, mul_one] at ht
  have hs := norm_linearInput_exponential_tail_le p Ω X hX hq δ c f hx hBx hXjet
    (fun j hj => hfjet 0 (by simp) j (by omega)) hδ
  simp only [exponentialPolynomialTail, map_sub, LinearMap.sub_apply, Submodule.coe_sub,
    Pi.sub_apply] at hs
  change ‖(differentialWordEvaluation Ω Y hY (wordPolynomialExp (linearWordPolynomial c) s) f).val (α 0) - _‖ ≤ _ at hs
  rw [he] at hs
  exact (norm_sub_le_norm_sub_add_norm_sub _ _ _).trans
    ((add_le_add ht hs).trans_eq (by ring))
end RothschildStein.G3
