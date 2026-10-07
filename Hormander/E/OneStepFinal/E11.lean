-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import Hormander.E.OneStepFinal.EnergyLimit

@[expose] public section

noncomputable section

open MeasureTheory SchwartzMap

namespace Hormander.E
open Hormander.B

variable {N : ℕ}

/-- The square `θ²` of a real Schwartz cutoff. -/
def sqCutoff (θ : SchwartzMap (Carrier N) ℝ) : SchwartzMap (Carrier N) ℝ :=
  SchwartzMap.smulLeftCLM ℝ (θ : Carrier N → ℝ) θ

theorem sqCutoff_apply (θ : SchwartzMap (Carrier N) ℝ) (x : Carrier N) :
    sqCutoff θ x = θ x * θ x := by
  rw [sqCutoff, SchwartzMap.smulLeftCLM_apply_apply θ.hasTemperateGrowth]
  rfl

theorem realMult_sqCutoff (θ : SchwartzMap (Carrier N) ℝ) :
    realMultiplierOperator (sqCutoff θ) =
      (realMultiplierOperator θ).comp (realMultiplierOperator θ) := by
  apply LinearMap.ext; intro φ; ext x
  simp only [LinearMap.comp_apply, realMultiplierOperator_apply, sqCutoff_apply]
  push_cast; ring

theorem sqCutoff_eq_one {θ : SchwartzMap (Carrier N) ℝ} {x : Carrier N} (h : θ x = 1) :
    sqCutoff θ x = 1 := by rw [sqCutoff_apply, h]; norm_num

/-- Ring identity behind the commutator expansion. -/
theorem e10_ring {R : Type*} [Ring R] (L x m q : R) (hq : q = x * m - m * x) :
    L * (m * m) * x = x * (m * L * m) +
      ((L * m - m * L) * x * m + m * (L * x - x * L) * m - q * L * m - L * (m * q)) := by
  subst hq
  noncomm_ring

/-- The commutator remainder `R`. -/
def e11R (X : RealSchwartzVectorField N) (θ : SchwartzMap (Carrier N) ℝ) (r : ℝ) : Operator N :=
  (operatorComm (lambdaOperator r) (realMultiplierOperator θ)).comp
      ((vectorFieldOperator X).comp (realMultiplierOperator θ)) +
    (realMultiplierOperator θ).comp
      ((operatorComm (lambdaOperator r) (vectorFieldOperator X)).comp (realMultiplierOperator θ)) -
    (multiplierOperator (vectorFieldOperator X (complexifyRealSchwartz θ))).comp
      ((lambdaOperator r).comp (realMultiplierOperator θ)) -
    (lambdaOperator r).comp ((realMultiplierOperator θ).comp
      (multiplierOperator (vectorFieldOperator X (complexifyRealSchwartz θ))))

instance (X : RealSchwartzVectorField N) (θ : SchwartzMap (Carrier N) ℝ) (r : ℝ) :
    HCT (e11R X θ r) := by
  unfold e11R
  have hq : HCT (multiplierOperator (vectorFieldOperator X (complexifyRealSchwartz θ))) :=
    ⟨multiplierOperator_hasContinuousTranspose _⟩
  infer_instance

/-- The commutator expansion as an identity of operators on `𝓢`:
`Λ^r M_{θ²} X = X T^r + R`. -/
theorem e11_op (X : RealSchwartzVectorField N) (θ : SchwartzMap (Carrier N) ℝ) (r : ℝ) :
    (lambdaOperator r).comp ((realMultiplierOperator (sqCutoff θ)).comp (vectorFieldOperator X)) =
      (vectorFieldOperator X).comp (energyT θ r) + e11R X θ r := by
  have hq : multiplierOperator (vectorFieldOperator X (complexifyRealSchwartz θ)) =
      vectorFieldOperator X * realMultiplierOperator θ -
        realMultiplierOperator θ * vectorFieldOperator X := by
    have := operatorComm_vectorField_multiplier X (complexifyRealSchwartz θ)
    rw [← this]
    rfl
  have := e10_ring (lambdaOperator (N := N) r) (vectorFieldOperator X) (realMultiplierOperator θ)
    _ hq
  rw [realMult_sqCutoff]
  unfold energyT e11R operatorComm
  simp only [← Module.End.mul_eq_comp]
  simpa [mul_assoc] using this

theorem hasOrder_e11R (X : RealSchwartzVectorField N) (θ : SchwartzMap (Carrier N) ℝ) (r : ℝ) :
    HasOrder r (e11R X θ r) := by
  have hM : HasOrder 0 (realMultiplierOperator θ) := hasOrder_multiplierOperator_zero _
  have hq : HasOrder 0 (multiplierOperator (vectorFieldOperator X (complexifyRealSchwartz θ))) :=
    hasOrder_multiplierOperator_zero _
  have hΛ := hasOrder_lambdaOperator (N := N) r
  obtain ⟨h1, h2⟩ := eFacing_orders X θ r
  have p1 : HasOrder r ((operatorComm (lambdaOperator r) (realMultiplierOperator θ)).comp
      ((vectorFieldOperator X).comp (realMultiplierOperator θ))) := by
    have := (h1.comp hM)
    have e : ((operatorComm (lambdaOperator r) (realMultiplierOperator θ)).comp
        (vectorFieldOperator X)).comp (realMultiplierOperator θ) =
        (operatorComm (lambdaOperator r) (realMultiplierOperator θ)).comp
      ((vectorFieldOperator X).comp (realMultiplierOperator θ)) := LinearMap.comp_assoc _ _ _
    rw [e] at this
    simpa using this
  have p2 : HasOrder r ((realMultiplierOperator θ).comp
      ((operatorComm (lambdaOperator r) (vectorFieldOperator X)).comp
        (realMultiplierOperator θ))) := by
    have := hM.comp (h2.comp hM)
    simpa using this
  have p3 : HasOrder r ((multiplierOperator (vectorFieldOperator X (complexifyRealSchwartz θ))).comp
      ((lambdaOperator r).comp (realMultiplierOperator θ))) := by
    have := hq.comp (hΛ.comp hM)
    simpa using this
  have p4 : HasOrder r ((lambdaOperator r).comp ((realMultiplierOperator θ).comp
      (multiplierOperator (vectorFieldOperator X (complexifyRealSchwartz θ))))) := by
    have := hΛ.comp (hM.comp hq)
    simpa using this
  exact ((p1.add p2).sub p3).sub p4

theorem e11R_factor (X : RealSchwartzVectorField N) (θ η₂ : SchwartzMap (Carrier N) ℝ)
    (hθη : ∀ x ∈ tsupport (θ : Carrier N → ℝ), η₂ x = 1) (r : ℝ) :
    e11R X θ r = (e11R X θ r).comp (realMultiplierOperator η₂) := by
  have hθ : ∀ φ, realMultiplierOperator θ (realMultiplierOperator η₂ φ) =
      realMultiplierOperator θ φ := fun φ => LinearMap.congr_fun (mult_absorb θ η₂ hθη) φ
  have hq : ∀ φ, multiplierOperator (vectorFieldOperator X (complexifyRealSchwartz θ))
      (realMultiplierOperator η₂ φ) =
      multiplierOperator (vectorFieldOperator X (complexifyRealSchwartz θ)) φ := fun φ =>
    LinearMap.congr_fun (multiplier_absorb_of_tsupport _ η₂ (fun x hx => hθη x (by
      rw [← tsupport_complexifyRealSchwartz]
      exact tsupport_vectorField_subset X _ hx))) φ
  apply LinearMap.ext; intro φ
  simp only [e11R, LinearMap.add_apply, LinearMap.sub_apply, LinearMap.comp_apply, hθ, hq]

theorem Eop_id (u : Tempered N) : Eop (LinearMap.id : Operator N) u = u := by
  ext φ
  rw [Eop_apply HasContinuousTranspose.id HasBilinearTranspose.id]
  rfl

/-- Recovering membership in `H^r` from the Bessel potential being in `L²`. -/
theorem bdd_of_lambda {g : Tempered N} {B : ℝ} (r : ℝ)
    (h : Bdd 0 (Eop (lambdaOperator r) g) B) : Bdd r g B := by
  obtain ⟨v, hv, hn⟩ := h
  have hC : ∀ φ : TestFunction N, sobolevNorm r (lambdaOperator (-r) φ) ≤
      ((1 : NNReal) : ℝ) * sobolevNorm 0 φ := by
    intro φ
    rw [sobolevNorm_lambdaOperator]
    simp
  obtain ⟨w, hw, hwn⟩ := Eop_bdd_global (hct_lambda (-r)) (m := -r) (s := r) (r' := 0)
    (by ring) hC v
  refine ⟨w, ?_, ?_⟩
  · rw [hw, hv]
    have : Eop (lambdaOperator (-r)) (Eop (lambdaOperator r) g) = g := by
      rw [← ContinuousLinearMap.comp_apply, ← Eop_comp (hct_lambda _) (hct_lambda _),
        lambdaOperator_comp, neg_add_cancel, lambdaOperator_zero, Eop_id]
    exact this
  · simpa using hwn.trans (mul_le_mul_of_nonneg_left hn (by norm_num))

/-- `θ² X_j u ∈ H^r`. -/
theorem sqCutoff_Xj_mem {k : ℕ} (Vs : Fin (k + 1) → RealSchwartzVectorField N)
    (cs η₁ θ ρ η₂ : SchwartzMap (Carrier N) ℝ)
    (h₁ : Hormander.D.cutoffPrecedes (η₁ : Carrier N → ℝ) (θ : Carrier N → ℝ))
    (h₂ : Hormander.D.cutoffPrecedes (θ : Carrier N → ℝ) (ρ : Carrier N → ℝ))
    (h₃ : Hormander.D.cutoffPrecedes (ρ : Carrier N → ℝ) (η₂ : Carrier N → ℝ))
    (hA6 : MollifierConverse N) (r : ℝ) (j : Fin k) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (u : Tempered N) (a b : Hormander.A.SobolevSpace N r),
      a.toDistr = cutoffDistr η₂ u →
      b.toDistr = cutoffDistr η₂ (Eop (Hormander.C.diffusionOperator Vs cs) u) →
      ∃ w : Hormander.A.SobolevSpace N r,
        w.toDistr = cutoffDistr (sqCutoff θ) (Eop (vectorFieldOperator (Vs j.succ)) u) ∧
          ‖w‖ ≤ C * (‖a‖ + ‖b‖) := by
  have hθη : ∀ x ∈ tsupport (θ : Carrier N → ℝ), η₂ x = 1 :=
    plateau_of_precedes (Hormander.D.cutoffPrecedes.trans h₂ h₃)
  obtain ⟨C1, hC10, hC1⟩ := Xj_Tr_mem_L2 Vs cs η₁ θ ρ η₂ h₁ h₂ h₃ hA6 r j
  obtain ⟨CR, hCR0, hCR⟩ := Eop_bdd_family_uniform (fun _ : Unit => e11R (Vs j.succ) θ r)
    (fun _ => HCT.out) (hasOrder_e11R (Vs j.succ) θ r).uniform 0 (r' := r) (by simp) η₂
    (fun _ => e11R_factor (Vs j.succ) θ η₂ hθη r)
  refine ⟨C1 + CR, by positivity, fun u a b ha hb => ?_⟩
  obtain ⟨v, hv, hvn⟩ := hC1 u a b ha hb
  have hR := hCR () u a ha
  have hid : Eop (lambdaOperator r) (cutoffDistr (sqCutoff θ)
      (Eop (vectorFieldOperator (Vs j.succ)) u)) =
      Eop ((vectorFieldOperator (Vs j.succ)).comp (energyT θ r)) u +
        Eop (e11R (Vs j.succ) θ r) u := by
    have := congrArg (fun T : Operator N => Eop T u) (e11_op (Vs j.succ) θ r)
    rw [Eop_add HCT.out HCT.out, Eop_comp HCT.out HCT.out, Eop_comp HCT.out HCT.out,
      Eop_comp HCT.out HCT.out, Eop_realMult] at this
    rw [Eop_comp (hct_vf _) (hct_energyT θ r)]
    exact this
  have hB : Bdd 0 (Eop (lambdaOperator r) (cutoffDistr (sqCutoff θ)
      (Eop (vectorFieldOperator (Vs j.succ)) u))) ((C1 + CR) * (‖a‖ + ‖b‖)) := by
    rw [hid]
    have h1 : Bdd 0 (Eop ((vectorFieldOperator (Vs j.succ)).comp (energyT θ r)) u) ‖v‖ :=
      ⟨v, hv, le_rfl⟩
    refine (h1.add hR).mono ?_
    nlinarith [norm_nonneg a, norm_nonneg b]
  obtain ⟨w, hw, hwn⟩ := bdd_of_lambda r hB
  exact ⟨w, hw, hwn⟩

end Hormander.E
