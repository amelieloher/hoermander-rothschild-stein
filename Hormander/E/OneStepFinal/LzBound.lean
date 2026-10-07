-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import Hormander.E.OneStepFinal.E11

@[expose] public section

noncomputable section

open MeasureTheory SchwartzMap

namespace Hormander.E
open Hormander.B

variable {N : ℕ}

/-- The regularized localization `B_δ = S_δ M_{η₁}`. -/
def bOp (η₁ : SchwartzMap (Carrier N) ℝ) (δ : ℝ) (hδ : 0 < δ) : Operator N :=
  (mollOp N δ hδ).comp (realMultiplierOperator η₁)

instance (η₁ : SchwartzMap (Carrier N) ℝ) (δ : ℝ) (hδ : 0 < δ) : HCT (bOp η₁ δ hδ) := by
  unfold bOp; infer_instance

theorem bOp_factor (η₁ ζ : SchwartzMap (Carrier N) ℝ)
    (hz : ∀ x ∈ tsupport (η₁ : Carrier N → ℝ), ζ x = 1) (δ : ℝ) (hδ : 0 < δ) :
    bOp η₁ δ hδ = (bOp η₁ δ hδ).comp (realMultiplierOperator ζ) := by
  unfold bOp
  rw [LinearMap.comp_assoc (realMultiplierOperator ζ) (realMultiplierOperator η₁),
    mult_absorb η₁ ζ hz]

theorem uniformOrder_bOp (η₁ : SchwartzMap (Carrier N) ℝ) :
    UniformOrder 0 (fun d : PosScale => bOp η₁ d.1 d.2) := by
  have := (uniformOrder_mollOp (N := N)).comp_right
    (hasOrder_multiplierOperator_zero (complexifyRealSchwartz η₁))
  simpa [bOp, mollOpS, realMultiplierOperator] using this

/-- `B_δ g ∈ H^s` for `ζ g ∈ H^s`. -/
theorem bdd_bOp (η₁ ζ : SchwartzMap (Carrier N) ℝ)
    (hz : ∀ x ∈ tsupport (η₁ : Carrier N → ℝ), ζ x = 1) (s : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (d : PosScale) (g : Tempered N) (w : Hormander.A.SobolevSpace N s),
      w.toDistr = cutoffDistr ζ g → Bdd s (Eop (bOp η₁ d.1 d.2) g) (C * ‖w‖) :=
  Eop_bdd_family_uniform (fun d : PosScale => bOp η₁ d.1 d.2) (fun d => HCT.out)
    (uniformOrder_bOp η₁) s (by simp) ζ (fun d => bOp_factor η₁ ζ hz d.1 d.2)

theorem comm_comm_eq (X B : Operator N) :
    operatorComm X (operatorComm X B) = operatorComm (operatorComm B X) X := by
  unfold operatorComm
  simp only [← Module.End.mul_eq_comp]
  noncomm_ring

/-- Commutators of `B_δ` with a vector field. -/
theorem bdd_comm_bOp (Y : RealSchwartzVectorField N) (η₁ ζ : SchwartzMap (Carrier N) ℝ)
    (hz : ∀ x ∈ tsupport (η₁ : Carrier N → ℝ), ζ x = 1) (s : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (d : PosScale) (g : Tempered N) (w : Hormander.A.SobolevSpace N s),
      w.toDistr = cutoffDistr ζ g →
        Bdd s (Eop (operatorComm (vectorFieldOperator Y) (bOp η₁ d.1 d.2)) g) (C * ‖w‖) ∧
        Bdd s (Eop (operatorComm (vectorFieldOperator Y)
          (operatorComm (vectorFieldOperator Y) (bOp η₁ d.1 d.2))) g) (C * ‖w‖) := by
  obtain ⟨C, hC0, hC⟩ := mollifier_cutoff_commutator_bound Y η₁ ζ hz s
  obtain ⟨C1, hC10, hC1⟩ := Eop_bdd_family
    (fun d : PosScale => operatorComm (bOp η₁ d.1 d.2) (vectorFieldOperator Y))
    (fun d => HCT.out) (m := 0) (s := s) (r' := s) (by simp) ζ
    (fun d => LinearMap.ext fun φ => (hC d.1 d.2 φ).1.1) (C := C)
    (fun d φ => (hC d.1 d.2 φ).1.2)
  obtain ⟨C2, hC20, hC2⟩ := Eop_bdd_family
    (fun d : PosScale => operatorComm (operatorComm (bOp η₁ d.1 d.2) (vectorFieldOperator Y))
      (vectorFieldOperator Y))
    (fun d => HCT.out) (m := 0) (s := s) (r' := s) (by simp) ζ
    (fun d => LinearMap.ext fun φ => (hC d.1 d.2 φ).2.1) (C := C)
    (fun d φ => (hC d.1 d.2 φ).2.2)
  refine ⟨max C1 C2, le_max_of_le_left hC10, fun d g w hw => ⟨?_, ?_⟩⟩
  · have e : operatorComm (vectorFieldOperator Y) (bOp η₁ d.1 d.2) =
        (-1 : ℂ) • operatorComm (bOp η₁ d.1 d.2) (vectorFieldOperator Y) :=
      operatorComm_antisymm _ _
    have h1 := (hC1 d g w hw).smul (-1 : ℂ)
    rw [norm_neg, norm_one, one_mul] at h1
    rw [e, Eop_smul _ HCT.out, smul_apply]
    exact h1.mono (mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _))
  · rw [comm_comm_eq]
    exact (hC2 d g w hw).mono (mul_le_mul_of_nonneg_right (le_max_right _ _) (norm_nonneg _))


theorem realMult_comm (g a : SchwartzMap (Carrier N) ℝ) :
    (realMultiplierOperator g).comp (realMultiplierOperator a) =
      (realMultiplierOperator a).comp (realMultiplierOperator g) := by
  apply LinearMap.ext; intro φ; ext x
  simp only [LinearMap.comp_apply, realMultiplierOperator_apply]
  ring

theorem comm_mult_factor (S : Operator N) (c ζ : SchwartzMap (Carrier N) ℝ)
    (hS : S = S.comp (realMultiplierOperator ζ)) :
    operatorComm (realMultiplierOperator c) S =
      (operatorComm (realMultiplierOperator c) S).comp (realMultiplierOperator ζ) := by
  have h : S.comp ((realMultiplierOperator c).comp (realMultiplierOperator ζ)) =
      S.comp (realMultiplierOperator c) := by
    rw [realMult_comm c ζ, ← LinearMap.comp_assoc, ← hS]
  unfold operatorComm
  rw [LinearMap.sub_comp, LinearMap.comp_assoc, ← hS, LinearMap.comp_assoc, h]

/-- The commutator `[M_c, B_δ]` has order zero, uniformly. -/
theorem bdd_comm_mult_bOp (c η₁ ζ : SchwartzMap (Carrier N) ℝ)
    (hz : ∀ x ∈ tsupport (η₁ : Carrier N → ℝ), ζ x = 1) (s : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (d : PosScale) (g : Tempered N) (w : Hormander.A.SobolevSpace N s),
      w.toDistr = cutoffDistr ζ g →
        Bdd s (Eop (operatorComm (realMultiplierOperator c) (bOp η₁ d.1 d.2)) g) (C * ‖w‖) := by
  have hc : HasOrder 0 (realMultiplierOperator c) :=
    hasOrder_multiplierOperator_zero (complexifyRealSchwartz c)
  have h1 : UniformOrder (0 + 0) (fun d : PosScale =>
      (realMultiplierOperator c).comp (bOp η₁ d.1 d.2)) := (uniformOrder_bOp η₁).comp_left hc
  have h2 : UniformOrder (0 + 0) (fun d : PosScale =>
      (bOp η₁ d.1 d.2).comp (realMultiplierOperator c)) := (uniformOrder_bOp η₁).comp_right hc
  have h3 : UniformOrder 0 (fun d : PosScale =>
      operatorComm (realMultiplierOperator c) (bOp η₁ d.1 d.2)) := by
    simpa [operatorComm] using h1.sub h2
  exact Eop_bdd_family_uniform (fun d : PosScale =>
    operatorComm (realMultiplierOperator c) (bOp η₁ d.1 d.2)) (fun d => HCT.out) h3 s
    (by simp) ζ (fun d => comm_mult_factor _ c ζ (bOp_factor η₁ ζ hz d.1 d.2))


/-- the finite bound on `‖L z_δ‖_{H^r}` for `z_δ = S_δ(η₁ u)`. -/
theorem Lz_bound {k : ℕ} (Vs : Fin (k + 1) → RealSchwartzVectorField N)
    (cs η₁ θ ρ η₂ : SchwartzMap (Carrier N) ℝ)
    (h₁ : Hormander.D.cutoffPrecedes (η₁ : Carrier N → ℝ) (θ : Carrier N → ℝ))
    (h₂ : Hormander.D.cutoffPrecedes (θ : Carrier N → ℝ) (ρ : Carrier N → ℝ))
    (h₃ : Hormander.D.cutoffPrecedes (ρ : Carrier N → ℝ) (η₂ : Carrier N → ℝ))
    (hA6 : MollifierConverse N) (r : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (d : PosScale) (u : Tempered N) (a b : Hormander.A.SobolevSpace N r),
      a.toDistr = cutoffDistr η₂ u →
      b.toDistr = cutoffDistr η₂ (Eop (Hormander.C.diffusionOperator Vs cs) u) →
      Bdd r (Eop (Hormander.C.diffusionOperator Vs cs) (Eop (bOp η₁ d.1 d.2) u))
        (C * (‖a‖ + ‖b‖)) := by
  have hη₁θ := plateau_of_precedes h₁
  have hη₁κ : ∀ x ∈ tsupport (η₁ : Carrier N → ℝ), sqCutoff θ x = 1 :=
    fun x hx => sqCutoff_eq_one (hη₁θ x hx)
  have hη₁η : ∀ x ∈ tsupport (η₁ : Carrier N → ℝ), η₂ x = 1 :=
    plateau_of_precedes (Hormander.D.cutoffPrecedes.trans (Hormander.D.cutoffPrecedes.trans h₁ h₂) h₃)
  obtain ⟨C0, hC00, hC0⟩ := bdd_bOp η₁ η₂ hη₁η r
  choose Cw hCw0 hCw using fun j : Fin k => sqCutoff_Xj_mem Vs cs η₁ θ ρ η₂ h₁ h₂ h₃ hA6 r j
  choose CK hCK0 hCK using fun j : Fin k => bdd_comm_bOp (Vs j.succ) η₁ (sqCutoff θ) hη₁κ r
  choose CK' hCK'0 hCK' using fun j : Fin k => bdd_comm_bOp (Vs j.succ) η₁ η₂ hη₁η r
  obtain ⟨C3, hC30, hC3⟩ := bdd_comm_bOp (Vs 0) η₁ η₂ hη₁η r
  obtain ⟨C4, hC40, hC4⟩ := bdd_comm_mult_bOp cs η₁ η₂ hη₁η r
  refine ⟨C0 + ∑ j : Fin k, (2 * CK j * Cw j + CK' j) + C3 + C4, ?_, ?_⟩
  · have : 0 ≤ ∑ j : Fin k, (2 * CK j * Cw j + CK' j) :=
      Finset.sum_nonneg fun j _ => by have := hCK0 j; have := hCw0 j; have := hCK'0 j; positivity
    positivity
  intro d u a b ha hb
  set M := ‖a‖ + ‖b‖ with hM
  have ha_le : ‖a‖ ≤ M := by linarith [norm_nonneg b]
  have hb_le : ‖b‖ ≤ M := by linarith [norm_nonneg a]
  have hM0 : 0 ≤ M := by positivity
  have hdec := Eop_diffusion_comp_second Vs cs (bOp η₁ d.1 d.2) u
  rw [Eop_comp HCT.out HCT.out] at hdec
  have t1 : Bdd r (Eop (bOp η₁ d.1 d.2) (Eop (Hormander.C.diffusionOperator Vs cs) u))
      (C0 * ‖b‖) := hC0 d _ b hb
  have tj : ∀ j : Fin k, Bdd r ((2 : ℂ) • Eop (operatorComm (vectorFieldOperator (Vs j.succ))
        (bOp η₁ d.1 d.2)) (Eop (vectorFieldOperator (Vs j.succ)) u) +
      Eop (operatorComm (vectorFieldOperator (Vs j.succ))
        (operatorComm (vectorFieldOperator (Vs j.succ)) (bOp η₁ d.1 d.2))) u)
      (2 * CK j * Cw j * M + CK' j * M) := by
    intro j
    obtain ⟨wj, hwj, hwjn⟩ := hCw j u a b ha hb
    have h2 := ((hCK j d (Eop (vectorFieldOperator (Vs j.succ)) u) wj hwj).1).smul (2 : ℂ)
    have h3 := (hCK' j d u a ha).2
    refine (h2.add h3).mono ?_
    have e2 : ‖(2 : ℂ)‖ = 2 := by simp
    rw [e2]
    have := hCK0 j
    have := hCK'0 j
    have h4 : CK j * ‖wj‖ ≤ CK j * (Cw j * M) := by gcongr
    have h5 : CK' j * ‖a‖ ≤ CK' j * M := by gcongr
    nlinarith
  have t3 : Bdd r (Eop (operatorComm (vectorFieldOperator (Vs 0)) (bOp η₁ d.1 d.2)) u)
      (C3 * ‖a‖) := (hC3 d u a ha).1
  have t4 : Bdd r (Eop (operatorComm (realMultiplierOperator cs) (bOp η₁ d.1 d.2)) u)
      (C4 * ‖a‖) := hC4 d u a ha
  have hsum := Bdd.sum (s := r) Finset.univ _ _ (fun j (_ : j ∈ (Finset.univ : Finset (Fin k))) => tj j)
  have hall := (((t1.add hsum).add t3).add t4)
  have e : (Eop (Hormander.C.diffusionOperator Vs cs)) ((Eop (bOp η₁ d.1 d.2)) u) = _ := hdec
  rw [e]
  refine hall.mono ?_
  have hs : ∑ j : Fin k, (2 * CK j * Cw j * M + CK' j * M) =
      (∑ j : Fin k, (2 * CK j * Cw j + CK' j)) * M := by
    rw [Finset.sum_mul]; refine Finset.sum_congr rfl fun j _ => by ring
  rw [hs]
  have h3 : C3 * ‖a‖ ≤ C3 * M := by gcongr
  have h4 : C4 * ‖a‖ ≤ C4 * M := by gcongr
  have h0 : C0 * ‖b‖ ≤ C0 * M := by gcongr
  nlinarith

end Hormander.E
