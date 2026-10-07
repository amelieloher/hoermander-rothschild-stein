-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module
public import RothschildStein.G3.RescaledTimeOneEndpointJets
public import RothschildStein.G3.FiniteLieFields
@[expose] public section
noncomputable section
open Set TopologicalSpace
open scoped BigOperators
namespace RothschildStein.G3

/-- Bundle exact rescaled finite-Lie ODEs and endpoint jets on a supplied
coefficient/state domain, separating rescaling from the buffer construction. -/
theorem rescaled_finiteLie_flow_bundle {a s N Q : ℕ} {p : Fin a → ℕ+}
    (D : FreeModelData a s p) (Ω : Opens (Fin N → ℝ))
    (X : Fin a → (Fin N → ℝ) → (Fin N → ℝ))
    {U W : Set ((Fin (freeDimension a s p) → ℝ) × (Fin N → ℝ))}
    (hU : IsOpen U) {τ ε : ℝ} (hε : 0 < ε) (hετ : 4*ε < τ)
    (Φ : (((Fin (freeDimension a s p) → ℝ) × (Fin N → ℝ)) × ℝ) → (Fin N → ℝ))
    (hΦ : ContDiffOn ℝ (⊤ : ℕ∞) Φ (U ×ˢ Ioo (-τ) τ))
    (hODE : ∀ q ∈ U, Φ (q,0) = q.2 ∧ ∀ t ∈ Ioo (-τ) τ,
      Φ (q,t) ∈ Ω ∧ HasDerivAt (fun v => Φ (q,v))
        (∑ j, q.1 j • wordBracket X (modelBasisWord D j) (Φ (q,t))) t)
    (hjet : ∀ q ∈ U, ∀ t, |t| < ε → ∀ j, 1 ≤ j → j ≤ Q →
      ‖iteratedFDeriv ℝ j (fun z : ℝ × ((Fin (freeDimension a s p) → ℝ) × (Fin N → ℝ)) =>
        Φ (z.2,z.1)) (t,q)‖ ≤ 2*(1+ε⁻¹)^j)
    (hW : ∀ q ∈ W, coefficientRescalingMap (ε/4) q ∈ U) :
    let Ψ := Φ ∘ G4.flowScale (ε/4)
    let C := (Q.factorial : ℝ) * (2*(1+ε⁻¹)^Q) * (1+|(ε/4)⁻¹|)^Q
    ContDiffOn ℝ (⊤ : ℕ∞) Ψ (W ×ˢ Ioo (-2) 2) ∧
      (∀ f : formalSpan a s p, ∀ x, (D.basis.equivFun f,x) ∈ W →
        Ψ ((D.basis.equivFun f,x),0) = x ∧ ∀ t ∈ Ioo (-2 : ℝ) 2,
          Ψ ((D.basis.equivFun f,x),t) ∈ Ω ∧ HasDerivAt
            (fun v => Ψ ((D.basis.equivFun f,x),v))
            (finiteLieField D X f (Ψ ((D.basis.equivFun f,x),t))) t) ∧
      ∀ q ∈ W, ∀ n, 1 ≤ n → n ≤ Q →
        ‖iteratedFDeriv ℝ n (finiteLieTimeOneMap Ψ) q‖ ≤ C := by
  intro Ψ C
  refine ⟨(shortFlow_rescaled_timeOne_contDiffOn hε hετ Φ hΦ).mono
    (Set.prod_mono hW Subset.rfl),?_,?_⟩
  · intro f x hx
    have he := shortFlow_rescaled_timeOne_ode (Ω := (Ω : Set (Fin N → ℝ))) hε hετ
      (fun j => wordBracket X (modelBasisWord D j)) Φ hODE
      (D.basis.equivFun f,x) (hW _ hx)
    refine ⟨he.1,fun t ht => ⟨(he.2 t ht).1,?_⟩⟩
    simpa only [finiteLieField] using (he.2 t ht).2
  · intro q hq n hn hnQ
    have he := norm_rescaled_timeOne_endpoint_jet_le hU hε hετ Φ hΦ (hW q hq) hn hnQ hjet
    have hnf : (n.factorial : ℝ) ≤ (Q.factorial : ℝ) := by
      exact_mod_cast Nat.factorial_le hnQ
    have hp : (1+|(ε/4)⁻¹|)^n ≤ (1+|(ε/4)⁻¹|)^Q :=
      pow_le_pow_right₀ (by linarith [abs_nonneg (ε/4)⁻¹]) hnQ
    apply he.trans
    exact mul_le_mul
      (mul_le_mul_of_nonneg_right hnf (by positivity)) hp (by positivity) (by positivity)
end RothschildStein.G3
