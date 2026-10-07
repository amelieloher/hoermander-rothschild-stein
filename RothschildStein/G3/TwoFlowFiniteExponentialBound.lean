-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module
public import RothschildStein.G3.TwoFlowTaylorJetBound
public import RothschildStein.G3.ExponentialProductEvaluation
public import RothschildStein.G3.ExponentialProductTailBound
public import RothschildStein.G3.LinearInputExponentialTail
@[expose] public section
noncomputable section
open Set TopologicalSpace
open scoped BigOperators
namespace RothschildStein.G3

/-- Explicit coefficient constant in the rectangular Taylor bound. -/
def twoFlowTaylorCoefficientBound (R s : ℕ) (B F : ℝ) : ℝ :=
  (2 ^ R * B) ^ (s + 1) * F + ∑ k ∈ Finset.range (s + 1),
    |(k.factorial : ℝ)⁻¹| * ((2 ^ R * B) ^ (s + 1 + k) * F)

/-- Actual successive flows of two weighted linear inputs agree
with their finite BCH exponential operator up to |delta|^(s+1). Both
Taylor and discarded product-tail errors are proved from finite jets
(BB Lemma 9.22, pp. 413–414). -/
theorem two_integralCurves_finiteExponential_bound {a s W N R : ℕ}
    (p : Fin a → ℕ+) (Ω : Opens (Fin N → ℝ))
    (X : Fin a → (Fin N → ℝ) → (Fin N → ℝ))
    (hX : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (X i) Ω)
    (hq : ∀ i, (p i : ℕ) ≤ W) (δ : ℝ) (u v : Fin a → ℝ)
    (U V : (Fin N → ℝ) → (Fin N → ℝ))
    (hU : ContDiffOn ℝ (⊤ : ℕ∞) U Ω) (hV : ContDiffOn ℝ (⊤ : ℕ∞) V Ω)
    (hUcomb : U = fun x => ∑ i, u i • (δ ^ (p i : ℕ) • X i x))
    (hVcomb : V = fun x => ∑ i, v i • (δ ^ (p i : ℕ) • X i x))
    {a₀ b₀ c₀ d₀ Bv Bx F : ℝ} (α β : ℝ → (Fin N → ℝ))
    (hα : ∀ t ∈ Ioo a₀ b₀, HasDerivAt α (U (α t)) t)
    (hαmem : ∀ t ∈ Ioo a₀ b₀, α t ∈ Ω)
    (hβ : ∀ t ∈ Ioo c₀ d₀, HasDerivAt β (V (β t)) t)
    (hβmem : ∀ t ∈ Ioo c₀ d₀, β t ∈ Ω) (hβ₀ : β 0 = α 1)
    (hαseg : ∀ t ∈ Icc (0 : ℝ) 1, t ∈ Ioo a₀ b₀)
    (hβseg : ∀ t ∈ Icc (0 : ℝ) 1, t ∈ Ioo c₀ d₀)
    (f : smoothOnFunctions Ω) (hs : 2 * s + 1 ≤ R) (hBv : 0 ≤ Bv) (hBx : 0 ≤ Bx)
    (hδ : |δ| ≤ 1)
    (hUjet : ∀ t ∈ Icc (0 : ℝ) 1, ∀ j ≤ R, ‖iteratedFDeriv ℝ j U (α t)‖ ≤ |δ| * Bv)
    (hVαjet : ∀ t ∈ Icc (0 : ℝ) 1, ∀ j ≤ R, ‖iteratedFDeriv ℝ j V (α t)‖ ≤ |δ| * Bv)
    (hVβjet : ∀ t ∈ Icc (0 : ℝ) 1, ∀ j ≤ R, ‖iteratedFDeriv ℝ j V (β t)‖ ≤ |δ| * Bv)
    (hXjet : ∀ i, ∀ j ≤ 2 * s, ‖iteratedFDeriv ℝ j (X i) (α 0)‖ ≤ Bx)
    (hfαjet : ∀ t ∈ Icc (0 : ℝ) 1, ∀ j ≤ R, ‖iteratedFDeriv ℝ j f.val (α t)‖ ≤ F)
    (hfβjet : ∀ t ∈ Icc (0 : ℝ) 1, ∀ j ≤ R, ‖iteratedFDeriv ℝ j f.val (β t)‖ ≤ F) :
    ‖f.val (β 1) - (differentialWordEvaluation Ω (fun i => δ ^ (p i : ℕ) • X i)
      (fun i => ((hX i).const_smul (δ ^ (p i : ℕ))).congr (fun x _ => by ext j; rfl))
      (finitePolynomial (finiteExp (finiteBCH
        (truncateSeries (s := s) (p := p) (polynomialSeries a (linearWordPolynomial u)))
        (truncateSeries (s := s) (p := p) (polynomialSeries a (linearWordPolynomial v)))))) f).val (α 0)‖ ≤
      |δ| ^ (s + 1) * (twoFlowTaylorCoefficientBound R s Bv F +
        exponentialProductTailCoefficientBound s W p (linearWordPolynomial u) (linearWordPolynomial v) Bx F) := by
  let Y := fun i => δ ^ (p i : ℕ) • X i
  have hY : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (Y i) Ω :=
    fun i => ((hX i).const_smul (δ ^ (p i : ℕ))).congr (fun x _ => by ext j; rfl)
  have hx : α 0 ∈ Ω := hαmem 0 (hαseg 0 (by simp))
  have hopU : differentialWordEvaluation Ω Y hY (linearWordPolynomial u) = smoothFieldOperator Ω U hU := by
    subst U
    exact differentialWordEvaluation_linearWordPolynomial Ω Y hY u
  have hopV : differentialWordEvaluation Ω Y hY (linearWordPolynomial v) = smoothFieldOperator Ω V hV := by
    subst V
    exact differentialWordEvaluation_linearWordPolynomial Ω Y hY v
  have he := differentialWordEvaluation_exponentialProduct Ω Y hY _ _ U V hU hV hopU hopV s s f hx
  have hb := two_integralCurves_taylor_bound_of_small_jets Ω U V hU hV α β hα hαmem hβ hβmem hβ₀
    hαseg hβseg f.val f.property hs hBv hδ hUjet hVαjet hVβjet hfαjet hfβjet
  rw [← he] at hb
  have ht := norm_exponentialProduct_tail_operator_le Ω X hX hq δ _ _
    (linearWordPolynomial_homogeneous u) (linearWordPolynomial_homogeneous v)
    (truncate_linearWordPolynomial_order p u) (truncate_linearWordPolynomial_order p v)
    f hx hBx hXjet (fun j hj => hfαjet 0 (by simp) j (by omega)) hδ
  simp only [exponentialProductPolynomialTail, map_sub, LinearMap.sub_apply,
    Submodule.coe_sub, Pi.sub_apply] at ht
  exact (norm_sub_le_norm_sub_add_norm_sub _ _ _).trans
    ((add_le_add hb ht).trans_eq (by unfold twoFlowTaylorCoefficientBound; ring))
end RothschildStein.G3
