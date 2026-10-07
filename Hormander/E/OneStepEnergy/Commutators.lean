-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import Hormander.B.Mollifier.EFacing
public import Hormander.B.Mollifier.Uncut
public import Hormander.B.Differential

@[expose] public section

noncomputable section
open MeasureTheory SchwartzMap
namespace Hormander.E
open Hormander.B
variable {N : ℕ}

/-- The energy multiplier `T^r = M_θ Λ^r M_θ`. -/
def energyT (θ : SchwartzMap (Carrier N) ℝ) (r : ℝ) : Operator N :=
  ((realMultiplierOperator θ).comp (lambdaOperator r)).comp (realMultiplierOperator θ)

/-- The mollified energy operator `A_δ = S_δ T^r`. -/
def energyA (θ : SchwartzMap (Carrier N) ℝ) (r : ℝ) (δ : ℝ) (hδ : 0 < δ) : Operator N :=
  (mollOp N δ hδ).comp (energyT θ r)

theorem hasOrder_energyT (θ : SchwartzMap (Carrier N) ℝ) (r : ℝ) : HasOrder r (energyT θ r) := by
  have h0 : HasOrder 0 (realMultiplierOperator θ) := hasOrder_multiplierOperator_zero _
  have := (h0.comp (hasOrder_lambdaOperator r)).comp h0
  simpa [energyT] using this

/-- `[Y, T^r]` has order `r`. -/
theorem hasOrder_comm_energyT (Y : RealSchwartzVectorField N) (θ : SchwartzMap (Carrier N) ℝ) (r : ℝ) :
    HasOrder r (operatorComm (vectorFieldOperator Y) (energyT θ r)) := by
  have h0 : HasOrder 0 (realMultiplierOperator θ) := hasOrder_multiplierOperator_zero _
  have hΛ := hasOrder_lambdaOperator (N := N) r
  have hYθ : HasOrder 0 (multiplierOperator (vectorFieldOperator Y (complexifyRealSchwartz θ))) :=
    hasOrder_multiplierOperator_zero _
  have hYΛ : HasOrder r (operatorComm (vectorFieldOperator Y) (lambdaOperator r)) := by
    have := fractional_diffOp_order r (isDiffOp_vectorFieldOperator Y)
    have h2 : operatorComm (vectorFieldOperator Y) (lambdaOperator r) =
        (-1 : ℂ) • operatorComm (lambdaOperator r) (vectorFieldOperator Y) :=
      operatorComm_antisymm _ _
    rw [h2]
    have h3 : HasOrder r (operatorComm (lambdaOperator r) (vectorFieldOperator Y)) := by
      convert this using 1; push_cast; ring
    exact h3.smul _
  have hMY : operatorComm (vectorFieldOperator Y) (realMultiplierOperator θ) =
      multiplierOperator (vectorFieldOperator Y (complexifyRealSchwartz θ)) :=
    operatorComm_vectorField_multiplier Y (complexifyRealSchwartz θ)
  unfold energyT
  rw [operatorComm_comp_right, operatorComm_comp_right, hMY]
  have hsum := (hYθ.comp hΛ).add (h0.comp hYΛ)
  have := (hsum.comp h0).add ((h0.comp hΛ).comp hYθ)
  simpa using this

theorem energyA_eq (θ : SchwartzMap (Carrier N) ℝ) (r : ℝ) (δ : ℝ) (hδ : 0 < δ) :
    energyA θ r δ hδ = ((mollOp N δ hδ).comp ((realMultiplierOperator θ).comp (lambdaOperator r))).comp
      (realMultiplierOperator θ) := by
  unfold energyA energyT
  simp only [LinearMap.comp_assoc]

/-- Uniform order `r` of `[Y, S_δ T^r]`. -/
theorem uniformOrder_comm_vf_energyA (Y : RealSchwartzVectorField N)
    (θ : SchwartzMap (Carrier N) ℝ) (r : ℝ) :
    UniformOrder r (fun d : PosScale => operatorComm (vectorFieldOperator Y)
      (energyA θ r d.1 d.2)) := by
  have h1 : UniformOrder 0 (fun d : PosScale => operatorComm (vectorFieldOperator Y) (mollOpS N d)) := by
    have := (uniformOrder_comm_moll_vectorField Y).smul (-1 : ℂ)
    convert this using 2 with d
    exact operatorComm_antisymm _ _
  have h2 := h1.comp_right (hasOrder_energyT θ r)
  have h3 := uniformOrder_mollOp (N := N)
  have h4 := h3.comp_right (hasOrder_comm_energyT Y θ r)
  have := h2.add h4
  simp only [zero_add] at this
  convert this using 2 with d
  unfold energyA
  rw [operatorComm_comp_right]
  rfl

/-- Right factorization of `[Y, S_δ T^r]` through `M_{η₂}`. -/
theorem comm_vf_energyA_factor (Y : RealSchwartzVectorField N) (θ η₂ : SchwartzMap (Carrier N) ℝ)
    (hθ : ∀ x ∈ tsupport (θ : Carrier N → ℝ), η₂ x = 1) (r : ℝ) (δ : ℝ) (hδ : 0 < δ) :
    operatorComm (vectorFieldOperator Y) (energyA θ r δ hδ) =
      (operatorComm (vectorFieldOperator Y) (energyA θ r δ hδ)).comp (realMultiplierOperator η₂) := by
  obtain ⟨_, h2⟩ := cutoff_identity_first_gen
    ((mollOp N δ hδ).comp ((realMultiplierOperator θ).comp (lambdaOperator r))) Y θ η₂ hθ
  rw [energyA_eq, operatorComm_antisymm (vectorFieldOperator Y), LinearMap.smul_comp]
  exact congrArg _ h2

/-- Uniform order `r` of `[M_c, S_δ T^r]`. -/
theorem uniformOrder_comm_mult_energyA (c θ : SchwartzMap (Carrier N) ℝ) (r : ℝ) :
    UniformOrder r (fun d : PosScale => operatorComm (realMultiplierOperator c)
      (energyA θ r d.1 d.2)) := by
  have hc : HasOrder 0 (realMultiplierOperator c) := hasOrder_multiplierOperator_zero _
  have hA : UniformOrder (0 + r) (fun d : PosScale => energyA θ r d.1 d.2) :=
    (uniformOrder_mollOp (N := N)).comp_right (hasOrder_energyT θ r)
  have h1 : UniformOrder r (fun d : PosScale => (realMultiplierOperator c).comp
      (energyA θ r d.1 d.2)) := by simpa using hA.comp_left hc
  have h2 : UniformOrder r (fun d : PosScale => (energyA θ r d.1 d.2).comp
      (realMultiplierOperator c)) := by simpa using hA.comp_right hc
  exact h1.sub h2

/-- Right factorization of `[M_c, S_δ T^r]` through `M_{η₂}`. -/
theorem comm_mult_energyA_factor (c θ η₂ : SchwartzMap (Carrier N) ℝ)
    (hθ : ∀ x ∈ tsupport (θ : Carrier N → ℝ), η₂ x = 1) (r : ℝ) (δ : ℝ) (hδ : 0 < δ) :
    operatorComm (realMultiplierOperator c) (energyA θ r δ hδ) =
      (operatorComm (realMultiplierOperator c) (energyA θ r δ hδ)).comp (realMultiplierOperator η₂) := by
  set S' := (mollOp N δ hδ).comp ((realMultiplierOperator θ).comp (lambdaOperator r)) with hS'
  have hcomm : operatorComm (realMultiplierOperator c) (realMultiplierOperator θ) = 0 :=
    multiplierOperator_comm _ _
  have h1 : operatorComm (realMultiplierOperator c) (energyA θ r δ hδ) =
      (operatorComm (realMultiplierOperator c) S').comp (realMultiplierOperator θ) := by
    rw [energyA_eq, operatorComm_comp_right, hcomm]
    simp
    rfl
  have habs : (realMultiplierOperator θ).comp (realMultiplierOperator η₂) = realMultiplierOperator θ :=
    multiplier_absorb_of_tsupport (complexifyRealSchwartz θ) η₂ (by
      rw [tsupport_complexifyRealSchwartz]; exact hθ)
  rw [h1, LinearMap.comp_assoc, habs]

/-- Uniform `L²` bounds and right factorization of the horizontal
commutators `[S_δ T^r, Y]` and `[[S_δ T^r, Y], Y]` through `M_{η₂}`. -/
theorem energyA_horizontal_bounds (Y : RealSchwartzVectorField N) (θ η₂ : SchwartzMap (Carrier N) ℝ)
    (hθ : ∀ x ∈ tsupport (θ : Carrier N → ℝ), η₂ x = 1) (r : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (δ : ℝ) (hδ : 0 < δ) (u : TestFunction N),
      operatorComm (energyA θ r δ hδ) (vectorFieldOperator Y) u =
        operatorComm (energyA θ r δ hδ) (vectorFieldOperator Y) (realMultiplierOperator η₂ u) ∧
      operatorComm (operatorComm (energyA θ r δ hδ) (vectorFieldOperator Y)) (vectorFieldOperator Y) u =
        operatorComm (operatorComm (energyA θ r δ hδ) (vectorFieldOperator Y)) (vectorFieldOperator Y)
          (realMultiplierOperator η₂ u) ∧
      sobolevNorm 0 (operatorComm (energyA θ r δ hδ) (vectorFieldOperator Y) u) ≤
        C * sobolevNorm r (realMultiplierOperator η₂ u) ∧
      sobolevNorm 0 (operatorComm (operatorComm (energyA θ r δ hδ) (vectorFieldOperator Y))
        (vectorFieldOperator Y) u) ≤ C * sobolevNorm r (realMultiplierOperator η₂ u) := by
  obtain ⟨C, hC0, hC⟩ := mollifier_weighted_commutator_bound Y θ η₂ hθ r
  refine ⟨C, hC0, fun δ hδ u => ?_⟩
  have e1 := (cutoff_identity_first_gen
    ((mollOp N δ hδ).comp ((realMultiplierOperator θ).comp (lambdaOperator r))) Y θ η₂ hθ).2
  have e2 := (cutoff_identity_second_gen
    ((mollOp N δ hδ).comp ((realMultiplierOperator θ).comp (lambdaOperator r))) Y θ η₂ hθ).2
  rw [← energyA_eq] at e1 e2
  have hb : sobolevNorm 0 (operatorComm (energyA θ r δ hδ) (vectorFieldOperator Y) u) +
      sobolevNorm 0 (operatorComm (operatorComm (energyA θ r δ hδ) (vectorFieldOperator Y))
        (vectorFieldOperator Y) u) ≤ C * sobolevNorm r (realMultiplierOperator η₂ u) := hC δ hδ u
  have n1 := sobolevNorm_nonneg 0 (operatorComm (energyA θ r δ hδ) (vectorFieldOperator Y) u)
  have n2 := sobolevNorm_nonneg 0 (operatorComm (operatorComm (energyA θ r δ hδ)
    (vectorFieldOperator Y)) (vectorFieldOperator Y) u)
  refine ⟨LinearMap.congr_fun e1 u, LinearMap.congr_fun e2 u, ?_, ?_⟩
  · linarith
  · linarith

end Hormander.E
