-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import Hormander.B.Mollifier.CutoffGen

@[expose] public section

noncomputable section

open MeasureTheory
open scoped FourierTransform ENNReal

namespace Hormander.B

variable {N : ℕ}

theorem HasOrder.sub {m : ℝ} {T U : Operator N} (hT : HasOrder m T) (hU : HasOrder m U) :
    HasOrder m (T - U) := by
  have := hT.add (hU.smul (-1 : ℂ))
  convert this using 1
  ext u : 1
  simp [sub_eq_add_neg]

theorem norm0_le_of_order {m : ℝ} {T : Operator N} (h : HasOrder m T) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ u, sobolevNorm 0 (T u) ≤ C * sobolevNorm m u := by
  obtain ⟨C, hC⟩ := h 0
  exact ⟨C, C.2, fun u => by simpa using hC u⟩

theorem operatorComm_comp_comm2 (A B V : Operator N) :
    operatorComm (operatorComm (A.comp B) V) V =
      A.comp (operatorComm (operatorComm B V) V) + (2 : ℂ) • (operatorComm A V).comp (operatorComm B V) +
        (operatorComm (operatorComm A V) V).comp B := by
  rw [operatorComm_comp_left, operatorComm_add_left, operatorComm_comp_left,
    operatorComm_comp_left, two_smul]
  abel

/-- Orders of the commutators of `Λ^s` with a real vector field. -/
theorem hasOrder_lambda_comm_vectorField (X : RealSchwartzVectorField N) (s : ℝ) :
    HasOrder s (operatorComm (lambdaOperator s) (vectorFieldOperator X)) ∧
      HasOrder s (operatorComm (operatorComm (lambdaOperator s) (vectorFieldOperator X))
        (vectorFieldOperator X)) := by
  have h := isDiffOp_vectorFieldOperator X
  refine ⟨?_, ?_⟩
  · have := fractional_diffOp_order s h
    convert this using 1; push_cast; ring
  · have := fractional_diffOp_nested_order s h h
    convert this using 1; push_cast; ring


/-- For `T^s = ζ₁ Λ^s ζ₁` and `ζ₂ = 1` near the
support of `ζ₁`:
`‖[S_δ T^s, X] u‖₂ + ‖[[S_δ T^s, X], X] u‖₂ ≤ C ‖ζ₂ u‖_{H^s}`, uniformly in `δ > 0`. -/
theorem mollifier_weighted_commutator_bound (X : RealSchwartzVectorField N)
    (z1 z2 : SchwartzMap (Carrier N) ℝ)
    (hz : ∀ x ∈ tsupport (z1 : Carrier N → ℝ), z2 x = 1) (s : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (δ : ℝ) (hδ : 0 < δ) (u : TestFunction N),
      sobolevNorm 0 (operatorComm ((mollOp N δ hδ).comp
          (((realMultiplierOperator z1).comp (lambdaOperator s)).comp (realMultiplierOperator z1)))
          (vectorFieldOperator X) u) +
        sobolevNorm 0 (operatorComm (operatorComm ((mollOp N δ hδ).comp
          (((realMultiplierOperator z1).comp (lambdaOperator s)).comp (realMultiplierOperator z1)))
          (vectorFieldOperator X)) (vectorFieldOperator X) u) ≤
        C * sobolevNorm s (realMultiplierOperator z2 u) := by
  set V := vectorFieldOperator X with hV
  set Λ := lambdaOperator (N := N) s with hΛ
  set M1 := realMultiplierOperator z1 with hM1def
  set M2 := realMultiplierOperator z2 with hM2def
  set z1c := complexifyRealSchwartz z1
  set Mv := multiplierOperator (vectorFieldOperator X z1c) with hMv
  set Mw := multiplierOperator (vectorFieldOperator X (vectorFieldOperator X z1c)) with hMw
  have hM1 : HasOrder 0 M1 := hasOrder_multiplierOperator_zero z1c
  have hM2 : HasOrder 0 M2 := hasOrder_multiplierOperator_zero (complexifyRealSchwartz z2)
  have hMv0 : HasOrder 0 Mv := hasOrder_multiplierOperator_zero _
  have hMw0 : HasOrder 0 Mw := hasOrder_multiplierOperator_zero _
  have hΛ0 : HasOrder s Λ := hasOrder_lambdaOperator s
  obtain ⟨hΛX, hΛXX⟩ := hasOrder_lambda_comm_vectorField X s
  -- B = Λ M1 and its commutators
  obtain ⟨g1, g1'⟩ := cutoff_identity_first_gen Λ X z1 z2 hz
  obtain ⟨g2, g2'⟩ := cutoff_identity_second_gen Λ X z1 z2 hz
  have hB : HasOrder s (Λ.comp M1) := by
    simpa using hΛ0.comp hM1
  have hB1 : HasOrder s (operatorComm (Λ.comp M1) V) := by
    rw [g1]
    have := (hΛX.comp hM1).sub (hΛ0.comp hMv0)
    simpa using this
  have hB2 : HasOrder s (operatorComm (operatorComm (Λ.comp M1) V) V) := by
    rw [g2]
    have := (((hΛXX.comp hM1).sub ((hΛX.comp hMv0).smul (2 : ℂ)))).add (hΛ0.comp hMw0)
    simpa using this
  have hBabs : (Λ.comp M1) = (Λ.comp M1).comp M2 := by
    have h1 : M1.comp M2 = M1 :=
      multiplier_absorb_of_tsupport z1c z2 (by rw [tsupport_complexifyRealSchwartz]; exact hz)
    rw [LinearMap.comp_assoc, h1]
  -- constants
  obtain ⟨CB1, hCB1, hB1b⟩ := norm0_le_of_order hB1
  obtain ⟨CB2, hCB2, hB2b⟩ := norm0_le_of_order hB2
  have hMB : HasOrder s (M2.comp (Λ.comp M1)) := by simpa using hM2.comp hB
  have hMB1 : HasOrder s (M2.comp (operatorComm (Λ.comp M1) V)) := by simpa using hM2.comp hB1
  obtain ⟨CM1, hCM1, hM1b⟩ := norm0_le_of_order hMB
  obtain ⟨CM2, hCM2, hM2b⟩ := norm0_le_of_order hMB1
  obtain ⟨Ce, hCe, hCe'⟩ := mollifier_cutoff_commutator_bound X z1 z2 hz 0
  have uS := uniformOrder_mollOp (N := N)
  obtain ⟨CA, hA⟩ := (uS.comp_right hM1) 0
  refine ⟨CA * CB1 + Ce * CM1 + (CA * CB2 + 2 * (Ce * CM2) + Ce * CM1), by positivity, ?_⟩
  intro δ hδ u
  set w := M2 u with hw
  have hST : (mollOp N δ hδ).comp ((M1.comp Λ).comp M1) =
      ((mollOp N δ hδ).comp M1).comp (Λ.comp M1) := by
    simp only [LinearMap.comp_assoc]
  rw [hST]
  set A := (mollOp N δ hδ).comp M1 with hA'
  set B := Λ.comp M1 with hBdef
  have hAb : ∀ v, sobolevNorm 0 (A v) ≤ CA * sobolevNorm 0 v := fun v => by
    have := hA ⟨δ, hδ⟩ v
    simp only [add_zero] at this
    exact this
  have e1 : operatorComm B V u = operatorComm B V w := LinearMap.congr_fun g1' u
  have e2 : operatorComm (operatorComm B V) V u = operatorComm (operatorComm B V) V w :=
    LinearMap.congr_fun g2' u
  have e3 : B u = B w := LinearMap.congr_fun hBabs u
  have d1 := fun v => (hCe' δ hδ v).1
  have d2 := fun v => (hCe' δ hδ v).2
  -- first commutator
  have F1 : sobolevNorm 0 (operatorComm (A.comp B) V u) ≤
      (CA * CB1 + Ce * CM1) * sobolevNorm s w := by
    rw [operatorComm_comp_left, LinearMap.add_apply, LinearMap.comp_apply, LinearMap.comp_apply]
    refine (sobolevNorm_add_le 0 _ _).trans ?_
    have t1 : sobolevNorm 0 (A (operatorComm B V u)) ≤ CA * CB1 * sobolevNorm s w := by
      rw [e1]
      refine (hAb _).trans ?_
      have := hB1b w
      calc (CA : ℝ) * sobolevNorm 0 (operatorComm B V w) ≤ CA * (CB1 * sobolevNorm s w) :=
            mul_le_mul_of_nonneg_left this (by positivity)
        _ = _ := by ring
    have t2 : sobolevNorm 0 (operatorComm A V (B u)) ≤ Ce * CM1 * sobolevNorm s w := by
      have h1 := (d1 (B u)).2
      have h2 : realMultiplierOperator z2 (B u) = (M2.comp B) w := by rw [e3]; rfl
      rw [h2] at h1
      refine h1.trans ?_
      calc Ce * sobolevNorm 0 ((M2.comp B) w) ≤ Ce * (CM1 * sobolevNorm s w) :=
            mul_le_mul_of_nonneg_left (hM1b w) hCe
        _ = _ := by ring
    have t1' : sobolevNorm 0 ((mollOp N δ hδ) (M1 ((operatorComm B V) u))) ≤ _ := t1
    have t2' : sobolevNorm 0 ((operatorComm A V ∘ₗ B) u) ≤ _ := t2
    linarith
  have F2 : sobolevNorm 0 (operatorComm (operatorComm (A.comp B) V) V u) ≤
      (CA * CB2 + 2 * (Ce * CM2) + Ce * CM1) * sobolevNorm s w := by
    rw [operatorComm_comp_comm2, LinearMap.add_apply, LinearMap.add_apply, LinearMap.smul_apply,
      LinearMap.comp_apply, LinearMap.comp_apply, LinearMap.comp_apply]
    refine (sobolevNorm_add_le 0 _ _).trans ?_
    have t3 : sobolevNorm 0 (A (operatorComm (operatorComm B V) V u)) ≤ CA * CB2 * sobolevNorm s w := by
      rw [e2]
      refine (hAb _).trans ?_
      calc (CA : ℝ) * sobolevNorm 0 (operatorComm (operatorComm B V) V w) ≤ CA * (CB2 * sobolevNorm s w) :=
            mul_le_mul_of_nonneg_left (hB2b w) (by positivity)
        _ = _ := by ring
    have t4 : sobolevNorm 0 ((2 : ℂ) • (operatorComm A V) (operatorComm B V u)) ≤
        2 * (Ce * CM2) * sobolevNorm s w := by
      rw [sobolevNorm_smul]
      have h1 := (d1 (operatorComm B V u)).2
      have h2 : realMultiplierOperator z2 (operatorComm B V u) = (M2.comp (operatorComm B V)) w := by
        rw [e1]; rfl
      rw [h2] at h1
      have h3 : ‖(2 : ℂ)‖ = 2 := by simp
      rw [h3]
      calc 2 * sobolevNorm 0 ((operatorComm A V) (operatorComm B V u)) ≤
            2 * (Ce * sobolevNorm 0 ((M2.comp (operatorComm B V)) w)) :=
            mul_le_mul_of_nonneg_left h1 (by norm_num)
        _ ≤ 2 * (Ce * (CM2 * sobolevNorm s w)) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (hM2b w) hCe) (by norm_num)
        _ = _ := by ring
    have t5 : sobolevNorm 0 ((operatorComm (operatorComm A V) V) (B u)) ≤ Ce * CM1 * sobolevNorm s w := by
      have h1 := (d2 (B u)).2
      have h2 : realMultiplierOperator z2 (B u) = (M2.comp B) w := by rw [e3]; rfl
      rw [h2] at h1
      refine h1.trans ?_
      calc Ce * sobolevNorm 0 ((M2.comp B) w) ≤ Ce * (CM1 * sobolevNorm s w) :=
            mul_le_mul_of_nonneg_left (hM1b w) hCe
        _ = _ := by ring
    have s1 := sobolevNorm_add_le 0 ((mollOp N δ hδ) (M1 ((operatorComm (operatorComm B V) V) u)))
      ((2 : ℂ) • (operatorComm A V) (operatorComm B V u))
    have t3' : sobolevNorm 0 ((mollOp N δ hδ) (M1 ((operatorComm (operatorComm B V) V) u))) ≤ _ := t3
    have t4' : sobolevNorm 0 ((2 : ℂ) • (operatorComm A V) (operatorComm B V u)) ≤ _ := t4
    have t5' : sobolevNorm 0 ((operatorComm (operatorComm A V) V ∘ₗ B) u) ≤ _ := t5
    linarith
  linarith

end Hormander.B
