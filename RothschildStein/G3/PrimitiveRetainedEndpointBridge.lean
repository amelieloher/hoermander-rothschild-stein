-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module
public import RothschildStein.G3.PrimitiveFlowFromLieODE
public import RothschildStein.G3.SignedPrimitiveCoordinates
@[expose] public section
noncomputable section
open Set Metric TopologicalSpace
namespace RothschildStein.G3

/-- A primitive arc at its signed weighted time is exactly the retained
Lie-input endpoint, on the actual common local domain. -/
theorem primitiveFlowFromLieFamily_signed_endpoint {a s N : ℕ} {p : Fin a → ℕ+}
    (D : FreeModelData a s p) (Ω Ω₀ : Opens (Fin N → ℝ))
    (X : Fin a → (Fin N → ℝ) → (Fin N → ℝ))
    (hX : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (X i) Ω)
    (Φ : (((Fin (freeDimension a s p) → ℝ) × (Fin N → ℝ)) × ℝ) → (Fin N → ℝ))
    {σ κ : ℝ} (hκ : 0 < κ)
    (hODE : ∀ z : formalSpan a s p, D.basis.equivFun z ∈ ball 0 σ →
      ∀ x ∈ Ω₀, Φ ((D.basis.equivFun z,x),0) = x ∧
        ∀ t ∈ Ioo (-2 : ℝ) 2, Φ ((D.basis.equivFun z,x),t) ∈ Ω ∧
          HasDerivAt (fun v => Φ ((D.basis.equivFun z,x),v))
            (finiteLieField D X z (Φ ((D.basis.equivFun z,x),t))) t)
    (b : Fin a × Bool) (t : ℝ)
    (hcoeff : D.basis.equivFun (κ • (wordLieElement [b.1] : formalSpan a s p)) ∈ ball 0 σ)
    (ht : |signedPrimitiveTime p b t| < κ)
    (hd : dilatedInputCoordinates D (primitiveScheduleLieInput b) t ∈ ball 0 σ)
    {x : Fin N → ℝ} (hx : x ∈ Ω₀) :
    primitiveFlowFromLieFamily D Φ κ b.1 (x,signedPrimitiveTime p b t) =
      finiteLieTimeOneMap Φ (dilatedInputCoordinates D (primitiveScheduleLieInput b) t,x) := by
  have heq := dilatedInputCoordinates_signed_primitive D b t
  have hh : D.basis.equivFun (signedPrimitiveTime p b t • (wordLieElement [b.1] : formalSpan a s p)) ∈ ball 0 σ := by
    rw [← heq]
    exact hd
  have he := finiteLie_endpoint_time_scaling D Ω Ω₀ X hX Φ hκ ht hODE
    (wordLieElement [b.1]) hcoeff hh hx
  exact he.trans (congrArg (fun c => finiteLieTimeOneMap Φ (c,x)) heq.symm)
end RothschildStein.G3
