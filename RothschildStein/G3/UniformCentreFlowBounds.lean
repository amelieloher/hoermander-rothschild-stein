-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module
public import RothschildStein.G3.FiniteLieEndpointDisplacement
@[expose] public section
noncomputable section
open Set Metric TopologicalSpace
namespace RothschildStein.G3

/-- Uniform actual flows with endpoint jets and displacement linear in
coefficients, using a common numerical domain for the full centre set. -/
theorem exists_uniform_centre_timeOne_flow_bounds {a s N R Q : ℕ} {p : Fin a → ℕ+}
    (D : FreeModelData a s p) {r B : ℝ} (hr : 0 < r) (hB : 0 ≤ B)
    (hQR : Q+s ≤ R+1) (hQ : 1 ≤ Q) :
    ∃ σ C : ℝ, 0 < σ ∧ 0 < C ∧
      ∀ (K : Set (Fin N → ℝ)) (X : Fin a → (Fin N → ℝ) → (Fin N → ℝ)),
        (∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (X i) (centreBuffer K r)) →
        (∀ x ∈ centreBuffer K r, ∀ i j, j ≤ R →
          ‖iteratedFDeriv ℝ j (X i) x‖ ≤ B) →
        ∃ Ψ : (((Fin (freeDimension a s p) → ℝ) × (Fin N → ℝ)) × ℝ) → (Fin N → ℝ),
          ContDiffOn ℝ (⊤ : ℕ∞) Ψ
            ((ball 0 σ ×ˢ (centreBuffer K (r/2) : Set (Fin N → ℝ))) ×ˢ Ioo (-2) 2) ∧
          (∀ f : formalSpan a s p, D.basis.equivFun f ∈ ball 0 σ →
            ∀ x ∈ centreBuffer K (r/2), Ψ ((D.basis.equivFun f,x),0) = x ∧
              ∀ t ∈ Ioo (-2 : ℝ) 2, Ψ ((D.basis.equivFun f,x),t) ∈ centreBuffer K r ∧
                HasDerivAt (fun v => Ψ ((D.basis.equivFun f,x),v))
                  (finiteLieField D X f (Ψ ((D.basis.equivFun f,x),t))) t) ∧
          ∀ q ∈ ball 0 σ ×ˢ (centreBuffer K (r/2) : Set (Fin N → ℝ)),
            (∀ n, 1 ≤ n → n ≤ Q → ‖iteratedFDeriv ℝ n (finiteLieTimeOneMap Ψ) q‖ ≤ C) ∧
              ‖finiteLieTimeOneMap Ψ q-q.2‖ ≤ C*‖q.1‖ := by
  obtain ⟨σ,C,hσ,hC,hflow⟩ := exists_uniform_centre_timeOne_jet_flow
    (N := N) D hr hB hQR
  refine ⟨σ,C,hσ,hC,?_⟩
  intro K X hX hXjet
  obtain ⟨Ψ,hΨ,hODE,hjets⟩ := hflow K X hX hXjet
  refine ⟨Ψ,hΨ,hODE,?_⟩
  intro q hq
  refine ⟨hjets q hq,?_⟩
  exact norm_finiteLie_endpoint_displacement_of_ode_and_first_jets D X
    (centreBuffer K (r/2)).isOpen hσ Ψ hΨ
    (fun f hf x hx => ⟨(hODE f hf x hx).1,
      fun t ht => ((hODE f hf x hx).2 t ht).2⟩)
    (fun z hz => hjets z hz 1 le_rfl hQ) hq.1 hq.2
end RothschildStein.G3
