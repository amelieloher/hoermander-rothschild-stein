-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module
public import RothschildStein.G3.ZeroCoefficientFlow
@[expose] public section
noncomputable section
open Set Metric
namespace RothschildStein.G3

/-- The zero coefficient endpoint is the identity throughout the actual
initial-point domain, by the exact zero-field ODE. -/
theorem finiteLie_endpoint_zero_on_initial_domain {a s N : ℕ} {p : Fin a → ℕ+}
    (D : FreeModelData a s p) (X : Fin a → (Fin N → ℝ) → (Fin N → ℝ))
    {Ω : Set (Fin N → ℝ)} {σ : ℝ} (hσ : 0 < σ)
    (Φ : (((Fin (freeDimension a s p) → ℝ) × (Fin N → ℝ)) × ℝ) → (Fin N → ℝ))
    (hODE : ∀ f : formalSpan a s p, D.basis.equivFun f ∈ ball 0 σ →
      ∀ x ∈ Ω, Φ ((D.basis.equivFun f,x),0) = x ∧ ∀ t ∈ Ioo (-2 : ℝ) 2,
        HasDerivAt (fun v => Φ ((D.basis.equivFun f,x),v))
          (finiteLieField D X f (Φ ((D.basis.equivFun f,x),t))) t) :
    ∀ x ∈ Ω, finiteLieTimeOneMap Φ (0,x) = x := by
  intro x hx
  have he := hODE 0 (by simpa only [map_zero] using
    (show (0 : Fin (freeDimension a s p) → ℝ) ∈ ball 0 σ by simp [hσ])) x hx
  exact finiteLieTimeOneMap_zero_of_finiteLie_ode D X Φ x
    (by simpa only [map_zero] using he.1)
    (fun t ht => by simpa only [map_zero] using he.2 t ht)
end RothschildStein.G3
