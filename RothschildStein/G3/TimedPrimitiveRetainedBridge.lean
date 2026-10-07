-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module
public import RothschildStein.G3.TimedPrimitiveLieInputs
public import RothschildStein.G3.PrimitiveRetainedEndpointBridge
@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set Metric TopologicalSpace
namespace RothschildStein.G3

/-- A scaled fixed real time agrees exactly with the retained endpoint. -/
theorem primitiveFlowFromLieFamily_timed_endpoint {a s N : ℕ} {p : Fin a → ℕ+}
    (D : FreeModelData a s p) (Ω Ω₀ : Opens (Fin N → ℝ))
    (X : Fin a → (Fin N → ℝ) → (Fin N → ℝ))
    (hX : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (X i) Ω)
    (Φ : (((Fin (freeDimension a s p) → ℝ) × (Fin N → ℝ)) × ℝ) → (Fin N → ℝ))
    {σ κ : ℝ} (hκ : 0 < κ)
    (hODE : ∀ z : formalSpan a s p, D.basis.equivFun z ∈ ball 0 σ →
      ∀ x ∈ Ω₀, Φ ((D.basis.equivFun z,x),0) = x ∧
        ∀ v ∈ Ioo (-2 : ℝ) 2, Φ ((D.basis.equivFun z,x),v) ∈ Ω ∧
          HasDerivAt (fun w => Φ ((D.basis.equivFun z,x),w))
            (finiteLieField D X z (Φ ((D.basis.equivFun z,x),v))) v)
    (b : Fin a × ℝ) (t : ℝ)
    (hcoeff : D.basis.equivFun (κ • (wordLieElement [b.1] : formalSpan a s p)) ∈ ball 0 σ)
    (ht : |t^(p b.1 : ℕ)*b.2| < κ)
    (hd : dilatedInputCoordinates D (timedPrimitiveLieInput b) t ∈ ball 0 σ)
    {x : Fin N → ℝ} (hx : x ∈ Ω₀) :
    primitiveFlowFromLieFamily D Φ κ b.1 (x,t^(p b.1 : ℕ)*b.2) =
      finiteLieTimeOneMap Φ (dilatedInputCoordinates D (timedPrimitiveLieInput b) t,x) := by
  have heq := dilatedInputCoordinates_timedPrimitive D b t
  have hh : D.basis.equivFun ((t^(p b.1 : ℕ)*b.2) • (wordLieElement [b.1] : formalSpan a s p)) ∈ ball 0 σ := by
    rw [← heq]
    exact hd
  have he := finiteLie_endpoint_time_scaling D Ω Ω₀ X hX Φ hκ ht hODE
    (wordLieElement [b.1]) hcoeff hh hx
  exact he.trans (congrArg (fun c => finiteLieTimeOneMap Φ (c,x)) heq.symm)
end RothschildStein.G3
