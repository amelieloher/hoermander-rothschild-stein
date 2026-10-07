-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import Hormander.E.OneStepFinal.EnergyOps

@[expose] public section

noncomputable section

open MeasureTheory SchwartzMap

namespace Hormander.E
open Hormander.B

variable {N : ℕ}

theorem tsupport_realMult_subset (θ : SchwartzMap (Carrier N) ℝ) (φ : TestFunction N) :
    tsupport (realMultiplierOperator θ φ : Carrier N → ℂ) ⊆ tsupport (θ : Carrier N → ℝ) := by
  have h : (fun x => realMultiplierOperator θ φ x) =
      (complexifyRealSchwartz θ : Carrier N → ℂ) * (φ : Carrier N → ℂ) := by
    funext x
    rw [realMultiplierOperator_apply]; rfl
  have h2 : tsupport (realMultiplierOperator θ φ : Carrier N → ℂ) =
      tsupport ((complexifyRealSchwartz θ : Carrier N → ℂ) * (φ : Carrier N → ℂ)) := by
    congr 1
  rw [h2]
  exact (tsupport_mul_subset_left).trans (tsupport_complexifyRealSchwartz θ).subset

theorem realMult_eq_self_of_tsupport (ρ : SchwartzMap (Carrier N) ℝ) (ψ : TestFunction N)
    (h : ∀ x ∈ tsupport (ψ : Carrier N → ℂ), ρ x = 1) : realMultiplierOperator ρ ψ = ψ := by
  ext x
  rw [realMultiplierOperator_apply]
  by_cases hx : ψ x = 0
  · simp [hx]
  · have : x ∈ tsupport (ψ : Carrier N → ℂ) := subset_tsupport _ hx
    rw [h x this]; simp

theorem tsupport_energyT_subset (θ : SchwartzMap (Carrier N) ℝ) (r : ℝ) (φ : TestFunction N) :
    tsupport (energyT θ r φ : Carrier N → ℂ) ⊆ tsupport (θ : Carrier N → ℝ) :=
  tsupport_realMult_subset θ _

/-- The commutator term `Q_δ = [S_δ M_ρ, Y] T^r`. -/
def qOp (Y : RealSchwartzVectorField N) (θ ρ : SchwartzMap (Carrier N) ℝ) (r δ : ℝ)
    (hδ : 0 < δ) : Operator N :=
  (operatorComm ((mollOp N δ hδ).comp (realMultiplierOperator ρ)) (vectorFieldOperator Y)).comp
    (energyT θ r)

instance (Y : RealSchwartzVectorField N) (θ ρ : SchwartzMap (Carrier N) ℝ) (r δ : ℝ)
    (hδ : 0 < δ) : HCT (qOp Y θ ρ r δ hδ) := by
  unfold qOp; infer_instance

/-- The commutator identity at the level of operators on `𝓢`. -/
theorem e6_op (Y : RealSchwartzVectorField N) (θ ρ : SchwartzMap (Carrier N) ℝ)
    (hθρ : ∀ x ∈ tsupport (θ : Carrier N → ℝ), ρ x = 1) (r δ : ℝ) (hδ : 0 < δ) :
    (mollOp N δ hδ).comp ((vectorFieldOperator Y).comp (energyT θ r)) =
      (vectorFieldOperator Y).comp (energyA θ r δ hδ) + qOp Y θ ρ r δ hδ := by
  apply LinearMap.ext
  intro φ
  have h1 : realMultiplierOperator ρ (energyT θ r φ) = energyT θ r φ :=
    realMult_eq_self_of_tsupport ρ _ (fun x hx => hθρ x (tsupport_energyT_subset θ r φ hx))
  have h2 : realMultiplierOperator ρ (vectorFieldOperator Y (energyT θ r φ)) =
      vectorFieldOperator Y (energyT θ r φ) :=
    realMult_eq_self_of_tsupport ρ _ (fun x hx => hθρ x (tsupport_energyT_subset θ r φ
      (tsupport_vectorField_subset Y _ hx)))
  simp only [qOp, operatorComm, energyA, LinearMap.comp_apply, LinearMap.add_apply,
    LinearMap.sub_apply, h1, h2]
  abel

theorem cutoffSchwartz_eq {η : SchwartzMap (Carrier N) ℝ} {g : Carrier N → ℝ}
    (h : Hormander.D.cutoffPrecedes (η : Carrier N → ℝ) g) : cutoffSchwartz h = η := by
  ext x; exact cutoffSchwartz_apply h x

theorem cutoffSchwartzOuter_eq {f : Carrier N → ℝ} {η : SchwartzMap (Carrier N) ℝ}
    (h : Hormander.D.cutoffPrecedes f (η : Carrier N → ℝ)) : cutoffSchwartzOuter h = η := by
  ext x; exact cutoffSchwartzOuter_apply h x

theorem qOp_factor (Y : RealSchwartzVectorField N) (θ ρ η₂ : SchwartzMap (Carrier N) ℝ)
    (hθη : ∀ x ∈ tsupport (θ : Carrier N → ℝ), η₂ x = 1) (r δ : ℝ) (hδ : 0 < δ) :
    qOp Y θ ρ r δ hδ = (qOp Y θ ρ r δ hδ).comp (realMultiplierOperator η₂) := by
  unfold qOp
  rw [LinearMap.comp_assoc (realMultiplierOperator η₂) (energyT θ r), ← energyT_factor θ η₂ hθη]

/-- The remainder `Q_δ u ∈ L²` with a bound by `‖η₂ u‖_{H^r}`. -/
theorem bdd_qOp (Y : RealSchwartzVectorField N) {η₁ θ ρ η₂ : SchwartzMap (Carrier N) ℝ}
    (h₁ : Hormander.D.cutoffPrecedes (η₁ : Carrier N → ℝ) (θ : Carrier N → ℝ))
    (h₂ : Hormander.D.cutoffPrecedes (θ : Carrier N → ℝ) (ρ : Carrier N → ℝ))
    (h₃ : Hormander.D.cutoffPrecedes (ρ : Carrier N → ℝ) (η₂ : Carrier N → ℝ))
    (hθη : ∀ x ∈ tsupport (θ : Carrier N → ℝ), η₂ x = 1) (r : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (d : PosScale) (u : Tempered N) (w : Hormander.A.SobolevSpace N r),
      w.toDistr = cutoffDistr η₂ u → Bdd 0 (Eop (qOp Y θ ρ r d.1 d.2) u) (C * ‖w‖) := by
  obtain ⟨C, hC0, hC⟩ := eFacing_mollifier_cutoff_bound Y h₁ h₂ h₃ r
  rw [cutoffSchwartz_eq h₂, cutoffSchwartz_eq h₃, cutoffSchwartzOuter_eq h₃] at hC
  exact Eop_bdd_family (fun d : PosScale => qOp Y θ ρ r d.1 d.2) (fun d => HCT.out)
    (m := r) (s := 0) (r' := r) (by simp) η₂ (fun d => qOp_factor Y θ ρ η₂ hθη r d.1 d.2)
    (fun d φ => by simpa [qOp, energyT] using hC d.1 d.2 φ)

end Hormander.E
