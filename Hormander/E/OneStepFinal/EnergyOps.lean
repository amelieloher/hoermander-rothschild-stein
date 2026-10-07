-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import Hormander.E.OneStepFinal.LAlgebra
public import Hormander.E.OneStepFinal.Realize

@[expose] public section

noncomputable section

open MeasureTheory SchwartzMap

namespace Hormander.E
open Hormander.B

variable {N : ℕ}

/-- Absorption of an inner cutoff by an outer cutoff equal to one on its support. -/
theorem mult_absorb (ζ ψ : SchwartzMap (Carrier N) ℝ)
    (h : ∀ x ∈ tsupport (ζ : Carrier N → ℝ), ψ x = 1) :
    (realMultiplierOperator ζ).comp (realMultiplierOperator ψ) = realMultiplierOperator ζ :=
  multiplier_absorb_of_tsupport (complexifyRealSchwartz ζ) ψ (by
    rw [tsupport_complexifyRealSchwartz]; exact h)

theorem energyT_factor (θ η₂ : SchwartzMap (Carrier N) ℝ)
    (hθη : ∀ x ∈ tsupport (θ : Carrier N → ℝ), η₂ x = 1) (r : ℝ) :
    energyT θ r = (energyT θ r).comp (realMultiplierOperator η₂) := by
  unfold energyT
  rw [LinearMap.comp_assoc (realMultiplierOperator η₂) (realMultiplierOperator θ),
    mult_absorb θ η₂ hθη]

theorem energyA_factor (θ η₂ : SchwartzMap (Carrier N) ℝ)
    (hθη : ∀ x ∈ tsupport (θ : Carrier N → ℝ), η₂ x = 1) (r δ : ℝ) (hδ : 0 < δ) :
    energyA θ r δ hδ = (energyA θ r δ hδ).comp (realMultiplierOperator η₂) := by
  unfold energyA
  rw [LinearMap.comp_assoc, ← energyT_factor θ η₂ hθη]

theorem uniformOrder_energyA (θ : SchwartzMap (Carrier N) ℝ) (r : ℝ) :
    UniformOrder r (fun d : PosScale => energyA θ r d.1 d.2) := by
  have := (uniformOrder_mollOp (N := N)).comp_right (hasOrder_energyT θ r)
  simpa [energyA, mollOpS] using this

/-- `A_δ u ∈ L²` for `η₂ u ∈ H^r`, uniformly in `δ`. -/
theorem bdd_energyA (θ η₂ : SchwartzMap (Carrier N) ℝ)
    (hθη : ∀ x ∈ tsupport (θ : Carrier N → ℝ), η₂ x = 1) (r : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (d : PosScale) (u : Tempered N) (w : Hormander.A.SobolevSpace N r),
      w.toDistr = cutoffDistr η₂ u → Bdd 0 (Eop (energyA θ r d.1 d.2) u) (C * ‖w‖) :=
  Eop_bdd_family_uniform (fun d : PosScale => energyA θ r d.1 d.2) (fun d => HCT.out)
    (uniformOrder_energyA θ r) 0 (by simp) η₂ (fun d => energyA_factor θ η₂ hθη r d.1 d.2)

/-- `T^r u ∈ L²` for `η₂ u ∈ H^r`. -/
theorem bdd_energyT (θ η₂ : SchwartzMap (Carrier N) ℝ)
    (hθη : ∀ x ∈ tsupport (θ : Carrier N → ℝ), η₂ x = 1) (r : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (u : Tempered N) (w : Hormander.A.SobolevSpace N r),
      w.toDistr = cutoffDistr η₂ u → Bdd 0 (Eop (energyT θ r) u) (C * ‖w‖) := by
  obtain ⟨C, hC0, hC⟩ := Eop_bdd_family_uniform (fun _ : Unit => energyT θ r) (fun _ => HCT.out)
    ((hasOrder_energyT θ r).uniform) 0 (r' := r) (by simp) η₂ (fun _ => energyT_factor θ η₂ hθη r)
  exact ⟨C, hC0, fun u w hw => hC () u w hw⟩

/-- `[Y, A_δ] u ∈ L²`. -/
theorem bdd_comm_vf (Y : RealSchwartzVectorField N) (θ η₂ : SchwartzMap (Carrier N) ℝ)
    (hθη : ∀ x ∈ tsupport (θ : Carrier N → ℝ), η₂ x = 1) (r : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (d : PosScale) (u : Tempered N) (w : Hormander.A.SobolevSpace N r),
      w.toDistr = cutoffDistr η₂ u →
        Bdd 0 (Eop (operatorComm (vectorFieldOperator Y) (energyA θ r d.1 d.2)) u) (C * ‖w‖) :=
  Eop_bdd_family_uniform (fun d : PosScale =>
    operatorComm (vectorFieldOperator Y) (energyA θ r d.1 d.2)) (fun d => HCT.out)
    (uniformOrder_comm_vf_energyA Y θ r) 0 (by simp) η₂
    (fun d => comm_vf_energyA_factor Y θ η₂ hθη r d.1 d.2)

/-- `[M_c, A_δ] u ∈ L²`. -/
theorem bdd_comm_mult (c θ η₂ : SchwartzMap (Carrier N) ℝ)
    (hθη : ∀ x ∈ tsupport (θ : Carrier N → ℝ), η₂ x = 1) (r : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (d : PosScale) (u : Tempered N) (w : Hormander.A.SobolevSpace N r),
      w.toDistr = cutoffDistr η₂ u →
        Bdd 0 (Eop (operatorComm (realMultiplierOperator c) (energyA θ r d.1 d.2)) u) (C * ‖w‖) :=
  Eop_bdd_family_uniform (fun d : PosScale =>
    operatorComm (realMultiplierOperator c) (energyA θ r d.1 d.2)) (fun d => HCT.out)
    (uniformOrder_comm_mult_energyA c θ r) 0 (by simp) η₂
    (fun d => comm_mult_energyA_factor c θ η₂ hθη r d.1 d.2)

theorem operatorComm_smul_left' (c : ℂ) (A B : Operator N) :
    operatorComm (c • A) B = c • operatorComm A B := by
  unfold operatorComm
  rw [LinearMap.smul_comp, LinearMap.comp_smul, smul_sub]

/-- `[[Y, A_δ], Y] u ∈ L²`. -/
theorem bdd_comm2_vf (Y : RealSchwartzVectorField N) (θ η₂ : SchwartzMap (Carrier N) ℝ)
    (hθη : ∀ x ∈ tsupport (θ : Carrier N → ℝ), η₂ x = 1) (r : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (d : PosScale) (u : Tempered N) (w : Hormander.A.SobolevSpace N r),
      w.toDistr = cutoffDistr η₂ u →
        Bdd 0 (Eop (operatorComm (operatorComm (vectorFieldOperator Y) (energyA θ r d.1 d.2))
          (vectorFieldOperator Y)) u) (C * ‖w‖) := by
  obtain ⟨C, hC0, hC⟩ := energyA_horizontal_bounds Y θ η₂ hθη r
  obtain ⟨C', hC'0, hC'⟩ := Eop_bdd_family
    (fun d : PosScale => operatorComm (operatorComm (energyA θ r d.1 d.2) (vectorFieldOperator Y))
      (vectorFieldOperator Y)) (fun d => HCT.out) (m := r) (s := 0) (r' := r) (by simp) η₂
    (fun d => LinearMap.ext fun φ => (hC d.1 d.2 φ).2.1) (C := C)
    (fun d φ => (hC d.1 d.2 φ).2.2.2)
  refine ⟨C', hC'0, fun d u w hw => ?_⟩
  have e : operatorComm (operatorComm (vectorFieldOperator Y) (energyA θ r d.1 d.2))
      (vectorFieldOperator Y) = (-1 : ℂ) • operatorComm (operatorComm (energyA θ r d.1 d.2)
        (vectorFieldOperator Y)) (vectorFieldOperator Y) := by
    rw [operatorComm_antisymm (vectorFieldOperator Y), operatorComm_smul_left']
  have h1 := (hC' d u w hw).smul (-1 : ℂ)
  rw [norm_neg, norm_one, one_mul] at h1
  rw [e, Eop_smul _ HCT.out, smul_apply]
  exact h1

end Hormander.E
