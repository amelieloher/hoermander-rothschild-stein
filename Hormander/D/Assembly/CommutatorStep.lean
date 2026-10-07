-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import Hormander.D.CommExpansion
public import Hormander.D.LocalizedOrder
public import Hormander.C.Energy.Estimate
public import Hormander.B.Mollifier.Weighted
public import Hormander.B.Multipliers
public import Hormander.B.Fractional.DerivativeFacts

@[expose] public section

noncomputable section

namespace Hormander.D

open Hormander.B

/-- Triangle inequality for a finite sum in the `s`-Sobolev norm. -/
private theorem sobolevNorm_sum_le_finset {N : ℕ} {ι : Type*} (s : ℝ) (t : Finset ι)
    (f : ι → TestFunction N) :
    sobolevNorm s (∑ i ∈ t, f i) ≤ ∑ i ∈ t, sobolevNorm s (f i) := by
  classical
  induction t using Finset.induction_on with
  | empty => simp
  | insert a t ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    exact (sobolevNorm_add_le s _ _).trans (add_le_add le_rfl ih)

private theorem sobolevNorm_neg_eq {N : ℕ} (s : ℝ) (u : TestFunction N) :
    sobolevNorm s (-u) = sobolevNorm s u := by
  have h := sobolevNorm_smul s (-1 : ℂ) u
  simpa using h

/-- The commutator of a Schwartz multiplier with the localized Bessel operator is bounded in L²
by the localized data norm. -/
theorem multiplierLocalizedBesselComm_l2_bound {N : ℕ}
    (η₁ η' η₂ : SchwartzMap (Carrier N) ℝ) (σ : ℝ) (c : SchwartzMap (Carrier N) ℝ)
    (hη₁η' : cutoffPrecedes (η₁ : Carrier N → ℝ) (η' : Carrier N → ℝ))
    (hη'η₂ : cutoffPrecedes (η' : Carrier N → ℝ) (η₂ : Carrier N → ℝ)) :
    ∃ C : NNReal, ∀ v : TestFunction N,
      sobolevNorm 0 (operatorComm (realMultiplierOperator c)
          (localizedBesselOperator η₁ η' σ) v) ≤
        (C : ℝ) * sobolevNorm σ (realMultiplierOperator η₂ v) := by
  have hmult : HasOrder 0 (realMultiplierOperator c) := by
    change HasOrder 0 (multiplierOperator (complexifyRealSchwartz c))
    exact (peetre_and_multiplier_order (N := N)).2 _
  have hA := localizedBesselOperator_hasOrder η₁ η' σ
  have hcomm : HasOrder σ (operatorComm (realMultiplierOperator c)
      (localizedBesselOperator η₁ η' σ)) := by
    unfold operatorComm
    have h1 := hmult.comp hA
    have h2 := hA.comp hmult
    rw [zero_add] at h1
    rw [add_zero] at h2
    exact h1.sub h2
  have hfactor := (rightSupportFactorization η₁ η' η₂ σ (fun j : Fin 0 => (0 : Fin N → SchwartzMap (Carrier N) ℝ))
    (0 : Fin N → SchwartzMap (Carrier N) ℝ) c hη₁η' hη'η₂).2.2.2
  exact hasOrder_l2_bound_of_right_factorization _ η₂ σ hcomm hfactor


/-- The commutator of the diffusion operator with the localized Bessel operator is
controlled by the diagonal first-order terms plus the localized data norm. -/
theorem commutator_l2_bound {N k : ℕ} (V : Fin (k + 1) → RealSchwartzVectorField N)
    (cS : SchwartzMap (Carrier N) ℝ) (η₁ η' η₂ : SchwartzMap (Carrier N) ℝ) (σ : ℝ)
    (hη₁η' : cutoffPrecedes (η₁ : Carrier N → ℝ) (η' : Carrier N → ℝ))
    (hη'η₂ : cutoffPrecedes (η' : Carrier N → ℝ) (η₂ : Carrier N → ℝ)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ u : TestFunction N,
      sobolevNorm 0 (operatorComm (Hormander.C.diffusionOperator V cS)
          (localizedBesselOperator η₁ η' σ) u) ≤
        2 * ∑ j : Fin k, sobolevNorm 0 (vectorFieldOperator (V j.succ)
            (operatorComm (vectorFieldOperator (V j.succ)) (localizedBesselOperator η₁ η' σ) u)) +
          C * sobolevNorm σ (realMultiplierOperator η₂ u) := by
  classical
  obtain ⟨_, ⟨CU, hCU⟩, _⟩ := localizedBesselEnergyComm_l2_bounds η₁ η' η₂ σ
    (fun j : Fin k => V j.succ) (V 0) cS hη₁η' hη'η₂
  obtain ⟨CX, hCX⟩ := vectorFieldLocalizedBesselComm_l2_bound η₁ η' η₂ σ (V 0) hη₁η' hη'η₂
  obtain ⟨Cc, hCc⟩ := multiplierLocalizedBesselComm_l2_bound η₁ η' η₂ σ cS hη₁η' hη'η₂
  refine ⟨(k : ℝ) * CU + CX + Cc, by positivity, fun u => ?_⟩
  set A := localizedBesselOperator η₁ η' σ with hA
  have hexp := commutator_sum_squares_expansion
    (fun j : Fin k => vectorFieldOperator (V j.succ))
    (vectorFieldOperator (V 0)) (realMultiplierOperator cS) A
  have hL : Hormander.C.diffusionOperator V cS =
      (∑ j : Fin k, (vectorFieldOperator (V j.succ)).comp (vectorFieldOperator (V j.succ))) +
        vectorFieldOperator (V 0) + realMultiplierOperator cS := rfl
  have hT : ∀ j : Fin k, operatorComm (operatorComm (vectorFieldOperator (V j.succ)) A)
      (vectorFieldOperator (V j.succ)) u =
      -(operatorComm (vectorFieldOperator (V j.succ))
        (operatorComm (vectorFieldOperator (V j.succ)) A) u) := by
    intro j
    rw [operatorComm_antisymm]
    simp
  have hu : operatorComm (Hormander.C.diffusionOperator V cS) A u =
      (∑ j : Fin k, ((2 : ℂ) • vectorFieldOperator (V j.succ)
          (operatorComm (vectorFieldOperator (V j.succ)) A u) +
        (-(operatorComm (vectorFieldOperator (V j.succ))
          (operatorComm (vectorFieldOperator (V j.succ)) A) u)))) +
        operatorComm (vectorFieldOperator (V 0)) A u +
        operatorComm (realMultiplierOperator cS) A u := by
    rw [hL, hexp]
    simp only [LinearMap.add_apply, LinearMap.sum_apply, LinearMap.smul_apply,
      LinearMap.comp_apply, hT]
  have hterm : ∀ j : Fin k, sobolevNorm 0
      ((2 : ℂ) • vectorFieldOperator (V j.succ)
          (operatorComm (vectorFieldOperator (V j.succ)) A u) +
        (-(operatorComm (vectorFieldOperator (V j.succ))
          (operatorComm (vectorFieldOperator (V j.succ)) A) u))) ≤
      2 * sobolevNorm 0 (vectorFieldOperator (V j.succ)
          (operatorComm (vectorFieldOperator (V j.succ)) A u)) +
        (CU : ℝ) * sobolevNorm σ (realMultiplierOperator η₂ u) := by
    intro j
    refine (sobolevNorm_add_le _ _ _).trans ?_
    rw [sobolevNorm_smul, sobolevNorm_neg_eq]
    have h2 : ‖(2 : ℂ)‖ = 2 := by simp
    rw [h2]
    exact add_le_add le_rfl (hCU j j u)
  calc
    sobolevNorm 0 (operatorComm (Hormander.C.diffusionOperator V cS) A u)
        = sobolevNorm 0 ((∑ j : Fin k, ((2 : ℂ) • vectorFieldOperator (V j.succ)
          (operatorComm (vectorFieldOperator (V j.succ)) A u) +
        (-(operatorComm (vectorFieldOperator (V j.succ))
          (operatorComm (vectorFieldOperator (V j.succ)) A) u)))) +
        operatorComm (vectorFieldOperator (V 0)) A u +
        operatorComm (realMultiplierOperator cS) A u) := by rw [hu]
    _ ≤ sobolevNorm 0 (∑ j : Fin k, ((2 : ℂ) • vectorFieldOperator (V j.succ)
          (operatorComm (vectorFieldOperator (V j.succ)) A u) +
        (-(operatorComm (vectorFieldOperator (V j.succ))
          (operatorComm (vectorFieldOperator (V j.succ)) A) u)))) +
        sobolevNorm 0 (operatorComm (vectorFieldOperator (V 0)) A u) +
        sobolevNorm 0 (operatorComm (realMultiplierOperator cS) A u) :=
      (sobolevNorm_add_le _ _ _).trans
        (add_le_add (sobolevNorm_add_le _ _ _) le_rfl)
    _ ≤ (∑ j : Fin k, (2 * sobolevNorm 0 (vectorFieldOperator (V j.succ)
          (operatorComm (vectorFieldOperator (V j.succ)) A u)) +
        (CU : ℝ) * sobolevNorm σ (realMultiplierOperator η₂ u))) +
        (CX : ℝ) * sobolevNorm σ (realMultiplierOperator η₂ u) +
        (Cc : ℝ) * sobolevNorm σ (realMultiplierOperator η₂ u) := by
      refine add_le_add (add_le_add ((sobolevNorm_sum_le_finset _ _ _).trans
        (Finset.sum_le_sum fun j _ => hterm j)) (hCX u)) (hCc u)
    _ = 2 * ∑ j : Fin k, sobolevNorm 0 (vectorFieldOperator (V j.succ)
            (operatorComm (vectorFieldOperator (V j.succ)) A u)) +
          ((k : ℝ) * CU + CX + Cc) * sobolevNorm σ (realMultiplierOperator η₂ u) := by
      rw [Finset.sum_add_distrib, ← Finset.mul_sum]
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      ring

end Hormander.D

end
