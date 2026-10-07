-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module
public import RothschildStein.G3.NumericalPrimitiveRescaling
public import RothschildStein.G3.ActualQuasiExponentialPoints
public import RothschildStein.G3.GeneralLieCommonFlowJets
public import RothschildStein.G3.RetainedLiePointLists
public import RothschildStein.G3.UniformCentreFlowBounds
public import RothschildStein.G3.NestedCentreBuffers
public import RothschildStein.G3.EndpointZeroOnDomain
@[expose] public section
noncomputable section
open Set Metric TopologicalSpace
namespace RothschildStein.G3

theorem weightedPrimitiveArc_fromLie_eq_endpoint {a s N : ℕ} {p : Fin a → ℕ+}
    (D : FreeModelData a s p) (Ω Ω₀ : Opens (Fin N → ℝ))
    (X : Fin a → (Fin N → ℝ) → (Fin N → ℝ))
    (hX : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (X i) Ω)
    (Φ : (((Fin (freeDimension a s p) → ℝ) × (Fin N → ℝ)) × ℝ) → (Fin N → ℝ))
    {σ κ t : ℝ} (hκ : 0 < κ) (htκ : |t| < κ) (ht1 : |t| ≤ 1)
    (hODE : ∀ z : formalSpan a s p, D.basis.equivFun z ∈ ball 0 σ →
      ∀ x ∈ Ω₀, Φ ((D.basis.equivFun z,x),0) = x ∧
        ∀ v ∈ Ioo (-2 : ℝ) 2, Φ ((D.basis.equivFun z,x),v) ∈ Ω ∧
          HasDerivAt (fun w => Φ ((D.basis.equivFun z,x),w))
            (finiteLieField D X z (Φ ((D.basis.equivFun z,x),v))) v)
    (hcoeff : ∀ i : Fin a, D.basis.equivFun (κ • (wordLieElement [i] : formalSpan a s p)) ∈ ball 0 σ)
    (b : Fin a × Bool) {x : Fin N → ℝ} (hx : x ∈ Ω₀) :
    weightedPrimitiveArc p (primitiveFlowFromLieFamily D Φ κ) b (t,x) =
      finiteLieTimeOneMap Φ (dilatedInputCoordinates D (primitiveScheduleLieInput b) t,x) := by
  exact primitiveFlowFromLieFamily_signed_endpoint D Ω Ω₀ X hX Φ hκ hODE b t (hcoeff b.1)
    ((signedPrimitiveTime_abs_le p b ht1).trans_lt htκ)
    (dilated_signed_primitive_mem_ball D b hκ htκ.le ht1 (hcoeff b.1)) hx

/-- Identification is along the actual locally admissible trajectory. -/
theorem primitiveSchedule_fromLie_eq_retainedList {a s N : ℕ} {p : Fin a → ℕ+}
    (D : FreeModelData a s p) (Ω Ω₀ : Opens (Fin N → ℝ))
    (X : Fin a → (Fin N → ℝ) → (Fin N → ℝ))
    (hX : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (X i) Ω)
    (Φ : (((Fin (freeDimension a s p) → ℝ) × (Fin N → ℝ)) × ℝ) → (Fin N → ℝ))
    {σ κ t : ℝ} (hκ : 0 < κ) (htκ : |t| < κ) (ht1 : |t| ≤ 1)
    (hODE : ∀ z : formalSpan a s p, D.basis.equivFun z ∈ ball 0 σ →
      ∀ x ∈ Ω₀, Φ ((D.basis.equivFun z,x),0) = x ∧
        ∀ v ∈ Ioo (-2 : ℝ) 2, Φ ((D.basis.equivFun z,x),v) ∈ Ω ∧
          HasDerivAt (fun w => Φ ((D.basis.equivFun z,x),w))
            (finiteLieField D X z (Φ ((D.basis.equivFun z,x),v))) v)
    (hcoeff : ∀ i : Fin a, D.basis.equivFun (κ • (wordLieElement [i] : formalSpan a s p)) ∈ ball 0 σ)
    (S : List (Fin a × Bool)) (x : Fin N → ℝ)
    (hS : G1.FlowScheduleAdmissible (primitiveFlowFromLieFamily D Φ κ)
      (fun i t => t^(p i : ℕ)) (fun _ => (Ω₀ : Set (Fin N → ℝ))) (fun _ => κ) t S x) :
    G1.runSchedule (fun b => weightedPrimitiveArc p (primitiveFlowFromLieFamily D Φ κ) b ∘
      (fun y => (t,y))) S x =
      runRetainedLiePointList D Φ (S.map primitiveScheduleLieInput) t x := by
  induction S generalizing x with
  | nil => rfl
  | cons b S ih =>
    have he := weightedPrimitiveArc_fromLie_eq_endpoint D Ω Ω₀ X hX Φ hκ htκ ht1 hODE hcoeff b hS.1
    exact (ih _ hS.2.2.2).trans
      (congrArg (runRetainedLiePointList D Φ (S.map primitiveScheduleLieInput) t) he)
end RothschildStein.G3
