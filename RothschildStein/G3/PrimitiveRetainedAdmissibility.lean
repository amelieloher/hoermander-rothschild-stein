-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module
public import RothschildStein.G3.PrimitiveRetainedScheduleBridge
public import RothschildStein.G3.PrimitiveScheduleCoefficientBudget
@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set Metric TopologicalSpace
namespace RothschildStein.G3

/-- Actual retained endpoint travel places the primitive schedule in its
initial domains at every prefix, on the same genuine flow family. -/
theorem primitiveSchedule_fromLie_admissible_of_budget {a s N : ℕ} {p : Fin a → ℕ+}
    (D : FreeModelData a s p) (Ω Ω₀ : Opens (Fin N → ℝ))
    (X : Fin a → (Fin N → ℝ) → (Fin N → ℝ))
    (hX : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (X i) Ω)
    (Φ : (((Fin (freeDimension a s p) → ℝ) × (Fin N → ℝ)) × ℝ) → (Fin N → ℝ))
    {σ κ t ρ d : ℝ} (hκ : 0 < κ) (htκ : |t| < κ) (ht1 : |t| ≤ 1) (hd : 0 ≤ d)
    (hODE : ∀ z : formalSpan a s p, D.basis.equivFun z ∈ ball 0 σ →
      ∀ x ∈ Ω₀, Φ ((D.basis.equivFun z,x),0) = x ∧
        ∀ v ∈ Ioo (-2 : ℝ) 2, Φ ((D.basis.equivFun z,x),v) ∈ Ω ∧
          HasDerivAt (fun w => Φ ((D.basis.equivFun z,x),w))
            (finiteLieField D X z (Φ ((D.basis.equivFun z,x),v))) v)
    (hcoeff : ∀ i : Fin a, D.basis.equivFun (κ • (wordLieElement [i] : formalSpan a s p)) ∈ ball 0 σ)
    (S : List (Fin a × Bool)) (x y : Fin N → ℝ) (hball : ball x ρ ⊆ Ω₀)
    (htravel : ∀ b ∈ S, ∀ z ∈ ball x ρ, ‖finiteLieTimeOneMap Φ
      (dilatedInputCoordinates D (primitiveScheduleLieInput b) t,z)-z‖ ≤ d)
    (hbudget : ‖y-x‖ + S.length*d < ρ) :
    G1.FlowScheduleAdmissible (primitiveFlowFromLieFamily D Φ κ)
      (fun i t => t^(p i : ℕ)) (fun _ => (Ω₀ : Set (Fin N → ℝ))) (fun _ => κ) t S y := by
  induction S generalizing y with
  | nil => trivial
  | cons b S ih =>
    have hy : y ∈ ball x ρ := by
      rw [mem_ball,dist_eq_norm]
      have hn : 0 ≤ ((b::S).length : ℝ)*d := by positivity
      linarith
    have harc := weightedPrimitiveArc_fromLie_eq_endpoint D Ω Ω₀ X hX Φ hκ htκ ht1
      hODE hcoeff b (hball hy)
    have he := (norm_sub_le_norm_sub_add_norm_sub
      (finiteLieTimeOneMap Φ (dilatedInputCoordinates D (primitiveScheduleLieInput b) t,y)) y x).trans
      (add_le_add (htravel b List.mem_cons_self y hy) (le_refl ‖y-x‖))
    have hb : ‖finiteLieTimeOneMap Φ
        (dilatedInputCoordinates D (primitiveScheduleLieInput b) t,y)-x‖ + S.length*d < ρ := by
      simp only [List.length_cons,Nat.cast_add,Nat.cast_one] at hbudget
      nlinarith
    have hend : finiteLieTimeOneMap Φ
        (dilatedInputCoordinates D (primitiveScheduleLieInput b) t,y) ∈ ball x ρ := by
      rw [mem_ball,dist_eq_norm]
      have hn : 0 ≤ (S.length : ℝ)*d := by positivity
      linarith
    have htime : t^(p b.1 : ℕ) ∈ Ioo (-κ) κ := by
      apply abs_lt.mp
      have hh := signedPrimitiveTime_abs_le p (b.1,true) ht1
      change |t^(p b.1 : ℕ)| ≤ |t| at hh
      exact hh.trans_lt htκ
    refine ⟨hball hy,htime,?_,?_⟩
    · change weightedPrimitiveArc p (primitiveFlowFromLieFamily D Φ κ) b (t,y) ∈ Ω₀
      rw [harc]
      exact hball hend
    · change G1.FlowScheduleAdmissible _ _ _ _ t S
        (weightedPrimitiveArc p (primitiveFlowFromLieFamily D Φ κ) b (t,y))
      rw [harc]
      exact ih _ (fun c hc => htravel c (List.mem_cons_of_mem b hc)) hb
end RothschildStein.G3
