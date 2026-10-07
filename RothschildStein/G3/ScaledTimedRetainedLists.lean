-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module
public import RothschildStein.G3.RetainedLiePointLists
public import RothschildStein.G3.TimedPrimitiveRetainedBridge
public import RothschildStein.G3.WeightedTimedPrimitiveSchedules
public import RothschildStein.G3.TimedSchedulePathBounds
@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set Metric TopologicalSpace
namespace RothschildStein.G3

/-- Actual scaled real-time schedules equal their retained endpoint lists along
all prefixes in the original local initial domains. -/
theorem scaledTimedSchedule_fromLie_eq_retainedList {a s N : ℕ} {p : Fin a → ℕ+}
    (D : FreeModelData a s p) (Ω Ω₀ : Opens (Fin N → ℝ))
    (X : Fin a → (Fin N → ℝ) → (Fin N → ℝ))
    (hX : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (X i) Ω)
    (Φ : (((Fin (freeDimension a s p) → ℝ) × (Fin N → ℝ)) × ℝ) → (Fin N → ℝ))
    {σ κ t : ℝ} (hκ : 0 < κ)
    (hODE : ∀ z : formalSpan a s p, D.basis.equivFun z ∈ ball 0 σ →
      ∀ x ∈ Ω₀, Φ ((D.basis.equivFun z,x),0) = x ∧
        ∀ v ∈ Ioo (-2 : ℝ) 2, Φ ((D.basis.equivFun z,x),v) ∈ Ω ∧
          HasDerivAt (fun w => Φ ((D.basis.equivFun z,x),w))
            (finiteLieField D X z (Φ ((D.basis.equivFun z,x),v))) v)
    (hcoeff : ∀ i : Fin a, D.basis.equivFun (κ • (wordLieElement [i] : formalSpan a s p)) ∈ ball 0 σ)
    (S : List (Fin a × ℝ))
    (htime : ∀ b ∈ S, |t^(p b.1 : ℕ)*b.2| < κ)
    (hinput : ∀ b ∈ S, dilatedInputCoordinates D (timedPrimitiveLieInput b) t ∈ ball 0 σ)
    (x : Fin N → ℝ) (hx : x ∈ Ω₀)
    (hS : TimedScheduleInside (primitiveFlowFromLieFamily D Φ κ) Ω₀
      (scaleTimedPrimitiveSchedule p t S) x) :
    runTimedPrimitiveSchedule (primitiveFlowFromLieFamily D Φ κ)
      (scaleTimedPrimitiveSchedule p t S) x =
      runRetainedLiePointList D Φ (S.map timedPrimitiveLieInput) t x := by
  revert htime hinput x
  induction S with
  | nil => intro htime hinput x hx hS; rfl
  | cons b S ih =>
    intro htime hinput x hx hS
    have he := primitiveFlowFromLieFamily_timed_endpoint D Ω Ω₀ X hX Φ hκ hODE b t
      (hcoeff b.1) (htime b List.mem_cons_self) (hinput b List.mem_cons_self) hx
    have hx' : primitiveFlowFromLieFamily D Φ κ b.1 (x,t^(p b.1 : ℕ)*b.2) ∈ Ω₀ := by
      have hh := hS.1 1 (by norm_num : (1 : ℝ) ∈ Icc (0 : ℝ) 1)
      change primitiveFlowFromLieFamily D Φ κ b.1 (x,1*(t^(p b.1 : ℕ)*b.2)) ∈ Ω₀ at hh
      rw [one_mul] at hh
      exact hh
    exact (ih (fun c hc => htime c (List.mem_cons_of_mem b hc))
      (fun c hc => hinput c (List.mem_cons_of_mem b hc)) _ hx' hS.2).trans
      (congrArg (runRetainedLiePointList D Φ (S.map timedPrimitiveLieInput) t) he)
end RothschildStein.G3
