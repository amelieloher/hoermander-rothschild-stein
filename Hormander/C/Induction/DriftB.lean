-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import Hormander.C.Induction.DriftP
public import Hormander.C.Induction.Words

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section
open MeasureTheory SchwartzMap
open scoped ComplexConjugate
namespace Hormander.C
open Hormander.B
variable {N k : ℕ} {D : DriftData N k} {T : Operator N}

theorem DriftData.commWV (D : DriftData N k) (i : Fin (k + 1)) :
    operatorComm D.W (D.V i) = vectorFieldOperator (bracketField D.Y (D.X i)) :=
  operatorComm_vectorField_vectorField D.Y (D.X i)

namespace DriftHyp
variable (h : DriftHyp D T)
include h

theorem sU (i : Fin k) :
    SLe D (fun u => sobolevNorm (2 * D.α - 1) (operatorComm D.W (D.V i.succ) u)) := by
  refine (h.U_le i).mono fun u => ?_
  have : operatorComm D.W (D.V i.succ) u = (-1 : ℂ) • operatorComm (D.V i.succ) D.W u := by
    simp only [operatorComm, LinearMap.sub_apply, LinearMap.comp_apply]
    rw [neg_one_smul]; abel
  rw [this, sobolevNorm_smul]
  simp

/-- `B1`: `(W L u, T u)`. -/
theorem termB1 : SBound D (fun u => hermitianPairing (D.W (D.L u)) (T u)) := by
  have e : ∀ u, hermitianPairing (D.W (D.L u)) (T u) =
      -(hermitianPairing (D.L u) (T (D.W u)) + hermitianPairing (D.L u) (operatorComm D.W T u)) +
        hermitianPairing (D.L u) ((realMultiplierOperator (negDiv D.Y)).comp T u) := fun u => by
    have h1 := H_vectorField_left D.Y (D.L u) (T u)
    have h2 := apply_comm_split D.W T u
    change hermitianPairing (D.W (D.L u)) _ = _ at h1
    rw [h1]
    change -hermitianPairing (D.L u) (D.W (T u)) + _ = _
    rw [h2, H_add_right]
    rfl
  simp_rw [e]
  refine SBound.add (SBound.neg (SBound.add ?_ ?_)) ?_
  · exact SBound.right' h.F h.T_mem 0 (2 * D.α - 1) (by ring) h.sLu h.sWτ (B := fun u => D.W u)
  · exact SBound.right' h.F h.cls_commW 0 (2 * D.α - 1) (by ring) h.sLu
      (h.sn_nonpos h.τ_neg) (B := fun u => u)
  · exact SBound.right' h.F (h.cls_mulT _) 0 (2 * D.α - 1) (by ring) h.sLu
      (h.sn_nonpos h.τ_neg) (B := fun u => u)

/-- `B2`: `(W (c u), T u)`. -/
theorem termB2 : SBound D (fun u => hermitianPairing (D.W (realMultiplierOperator D.c u)) (T u)) := by
  have hL := operatorComm_vectorField_multiplier D.Y (complexifyRealSchwartz D.c)
  have e : ∀ u, hermitianPairing (D.W (realMultiplierOperator D.c u)) (T u) =
      hermitianPairing (D.W u) ((realMultiplierOperator D.c).comp T u) +
      hermitianPairing (multiplierOperator (vectorFieldOperator D.Y (complexifyRealSchwartz D.c)) u) (T u) :=
    fun u => by
    have h2 := apply_comm_split D.W (realMultiplierOperator D.c) u
    have h3 : operatorComm D.W (realMultiplierOperator D.c) u =
        multiplierOperator (vectorFieldOperator D.Y (complexifyRealSchwartz D.c)) u :=
      LinearMap.congr_fun hL u
    rw [h2, h3, H_add_left, H_realMultiplier_left]
    rfl
  simp_rw [e]
  refine SBound.add ?_ ?_
  · exact SBound.right' h.F (h.cls_mulT _) (2 * D.α - 1) 0 (by ring) h.sWτ h.sn (B := fun u => u)
  · have hA : SLe D (fun u => sobolevNorm (2 * D.α - 1)
        (multiplierOperator (vectorFieldOperator D.Y (complexifyRealSchwartz D.c)) u)) :=
      SLe.of_order (hasOrder_multiplierOperator_zero _) _
        (by simpa using h.sn_nonpos h.τ_neg) (B := fun u => u)
    exact SBound.right' h.F h.T_mem (2 * D.α - 1) 0 (by ring) hA h.sn (B := fun u => u)

theorem cls_mulmulT (g : SchwartzMap (Carrier N) ℝ) :
    OperatorClass (2 * D.α - 1) ((realMultiplierOperator g).comp ((realMultiplierOperator g).comp T)) := by
  simpa using h.F.comp_mem 0 _ _ _ (h.F.multiplier_mem g) (h.cls_mulT g)

/-- `E1`: `(Vᵢ Vᵢ W u, T u)`. -/
theorem termE1 {Ts : Operator N} (hTs : HasHermitianAdjoint T Ts)
    (hTsc : OperatorClass (2 * D.α - 1) Ts)
    (hP : ∀ i : Fin k, SBound D (fun u => hermitianPairing (D.V i.succ (Ts (D.W u))) (D.V i.succ u)))
    (i : Fin k) :
    SBound D (fun u => hermitianPairing (D.V i.succ (D.V i.succ (D.W u))) (T u)) := by
  have e : ∀ u, hermitianPairing (D.V i.succ (D.V i.succ (D.W u))) (T u) =
      -hermitianPairing (D.V i.succ (D.W u)) (D.V i.succ (T u)) +
        (-(hermitianPairing (D.W u) ((realMultiplierOperator (negDiv (D.X i.succ))).comp T (D.V i.succ u)) +
          hermitianPairing (D.W u) (operatorComm (D.V i.succ)
            ((realMultiplierOperator (negDiv (D.X i.succ))).comp T) u)) +
         hermitianPairing (D.W u) ((realMultiplierOperator (negDiv (D.X i.succ))).comp
           ((realMultiplierOperator (negDiv (D.X i.succ))).comp T) u)) := fun u => by
    have h1 := H_vectorField_left (D.X i.succ) (D.V i.succ (D.W u)) (T u)
    change hermitianPairing (D.V i.succ (D.V i.succ (D.W u))) _ = _ at h1
    rw [h1]
    congr 1
    have h2 := H_vectorField_left (D.X i.succ) (D.W u) (realMultiplierOperator (negDiv (D.X i.succ)) (T u))
    change hermitianPairing (D.V i.succ (D.W u)) _ = _ at h2
    rw [h2]
    have h3 := apply_comm_split (D.V i.succ) ((realMultiplierOperator (negDiv (D.X i.succ))).comp T) u
    change -hermitianPairing (D.W u) (D.V i.succ (realMultiplierOperator (negDiv (D.X i.succ)) (T u))) + _ = _
    rw [show D.V i.succ (realMultiplierOperator (negDiv (D.X i.succ)) (T u)) =
      D.V i.succ ((realMultiplierOperator (negDiv (D.X i.succ))).comp T u) from rfl, h3, H_add_right]
    rfl
  simp_rw [e]
  refine SBound.add (h.termDi hTs hTsc hP i).neg (SBound.add (SBound.neg (SBound.add ?_ ?_)) ?_)
  · exact SBound.right' h.F (h.cls_mulT _) (2 * D.α - 1) 0 (by ring) h.sWτ (h.sV i)
      (B := fun u => D.V i.succ u)
  · exact SBound.right' h.F (h.cls_commV_mulT _ _) (2 * D.α - 1) 0 (by ring) h.sWτ h.sn (B := fun u => u)
  · exact SBound.right' h.F (h.cls_mulmulT _) (2 * D.α - 1) 0 (by ring) h.sWτ h.sn (B := fun u => u)

/-- `E2`: `(U Vᵢ u, T u)` with `U = [W, Vᵢ]`. -/
theorem termE2 (i : Fin k) :
    SBound D (fun u => hermitianPairing (operatorComm D.W (D.V i.succ) (D.V i.succ u)) (T u)) := by
  set Ui := bracketField D.Y (D.X i.succ) with hUi
  have hU : operatorComm D.W (D.V i.succ) = vectorFieldOperator Ui := D.commWV i.succ
  have hcls : OperatorClass (2 * D.α - 1) (operatorComm (vectorFieldOperator Ui) T) :=
    h.F.comm_vectorField _ T Ui h.T_mem
  have e : ∀ u, hermitianPairing (operatorComm D.W (D.V i.succ) (D.V i.succ u)) (T u) =
      -(hermitianPairing (D.V i.succ u) (T (vectorFieldOperator Ui u)) +
        hermitianPairing (D.V i.succ u) (operatorComm (vectorFieldOperator Ui) T u)) +
      hermitianPairing (D.V i.succ u) ((realMultiplierOperator (negDiv Ui)).comp T u) := fun u => by
    rw [hU]
    have h1 := H_vectorField_left Ui (D.V i.succ u) (T u)
    have h2 := apply_comm_split (vectorFieldOperator Ui) T u
    rw [h1, h2, H_add_right]
    rfl
  simp_rw [e]
  have hUu : SLe D (fun u => sobolevNorm (2 * D.α - 1) (vectorFieldOperator Ui u)) := by
    have := h.sU i
    rw [hU] at this
    exact this
  refine SBound.add (SBound.neg (SBound.add ?_ ?_)) ?_
  · exact SBound.right' h.F h.T_mem 0 (2 * D.α - 1) (by ring) (h.sV i) hUu
      (B := fun u => vectorFieldOperator Ui u) (A := fun u => D.V i.succ u)
  · exact SBound.right' h.F hcls 0 (2 * D.α - 1) (by ring) (h.sV i) (h.sn_nonpos h.τ_neg)
      (B := fun u => u) (A := fun u => D.V i.succ u)
  · exact SBound.right' h.F (h.cls_mulT _) 0 (2 * D.α - 1) (by ring) (h.sV i) (h.sn_nonpos h.τ_neg)
      (B := fun u => u) (A := fun u => D.V i.succ u)

/-- `E3`: `(Vᵢ U u, T u)` with `U = [W, Vᵢ]`. -/
theorem termE3 (i : Fin k) :
    SBound D (fun u => hermitianPairing (D.V i.succ (operatorComm D.W (D.V i.succ) u)) (T u)) := by
  have e : ∀ u, hermitianPairing (D.V i.succ (operatorComm D.W (D.V i.succ) u)) (T u) =
      -(hermitianPairing (operatorComm D.W (D.V i.succ) u) (T (D.V i.succ u)) +
        hermitianPairing (operatorComm D.W (D.V i.succ) u) (operatorComm (D.V i.succ) T u)) +
      hermitianPairing (operatorComm D.W (D.V i.succ) u)
        ((realMultiplierOperator (negDiv (D.X i.succ))).comp T u) := fun u => by
    have h1 := H_vectorField_left (D.X i.succ) (operatorComm D.W (D.V i.succ) u) (T u)
    have h2 := apply_comm_split (D.V i.succ) T u
    change hermitianPairing (D.V i.succ _) _ = _ at h1
    rw [h1]
    change -hermitianPairing _ (D.V i.succ (T u)) + _ = _
    rw [h2, H_add_right]
    rfl
  simp_rw [e]
  refine SBound.add (SBound.neg (SBound.add ?_ ?_)) ?_
  · exact SBound.right' h.F h.T_mem (2 * D.α - 1) 0 (by ring) (h.sU i) (h.sV i)
      (B := fun u => D.V i.succ u) (A := fun u => operatorComm D.W (D.V i.succ) u)
  · exact SBound.right' h.F (h.cls_commV _) (2 * D.α - 1) 0 (by ring) (h.sU i) h.sn
      (B := fun u => u) (A := fun u => operatorComm D.W (D.V i.succ) u)
  · exact SBound.right' h.F (h.cls_mulT _) (2 * D.α - 1) 0 (by ring) (h.sU i) h.sn
      (B := fun u => u) (A := fun u => operatorComm D.W (D.V i.succ) u)

theorem termB3 {Ts : Operator N} (hTs : HasHermitianAdjoint T Ts)
    (hTsc : OperatorClass (2 * D.α - 1) Ts)
    (hP : ∀ i : Fin k, SBound D (fun u => hermitianPairing (D.V i.succ (Ts (D.W u))) (D.V i.succ u)))
    (i : Fin k) :
    SBound D (fun u => hermitianPairing (D.W (D.V i.succ (D.V i.succ u))) (T u)) := by
  have e : ∀ u, hermitianPairing (D.W (D.V i.succ (D.V i.succ u))) (T u) =
      hermitianPairing (D.V i.succ (D.V i.succ (D.W u))) (T u) +
      hermitianPairing (D.V i.succ (operatorComm D.W (D.V i.succ) u)) (T u) +
      hermitianPairing (operatorComm D.W (D.V i.succ) (D.V i.succ u)) (T u) := fun u => by
    have h1 := apply_comm_split D.W (D.V i.succ) (D.V i.succ u)
    have h2 := apply_comm_split D.W (D.V i.succ) u
    rw [h1, h2, map_add, H_add_left, H_add_left]
  simp_rw [e]
  exact ((h.termE1 hTs hTsc hP i).add (h.termE3 i)).add (h.termE2 i)

theorem termB {Ts : Operator N} (hTs : HasHermitianAdjoint T Ts)
    (hTsc : OperatorClass (2 * D.α - 1) Ts)
    (hP : ∀ i : Fin k, SBound D (fun u => hermitianPairing (D.V i.succ (Ts (D.W u))) (D.V i.succ u))) :
    SBound D (fun u => hermitianPairing (D.W (D.V 0 u)) (T u)) := by
  have hV0 : ∀ u, D.V 0 u = D.L u - (∑ i : Fin k, D.V i.succ (D.V i.succ u)) -
      realMultiplierOperator D.c u := fun u => by
    have hL : D.L u = (∑ i : Fin k, D.V i.succ (D.V i.succ u)) + D.V 0 u + realMultiplierOperator D.c u := by
      unfold DriftData.L diffusionOperator DriftData.V
      simp only [LinearMap.add_apply, LinearMap.sum_apply, LinearMap.comp_apply]
    rw [hL]; abel
  have e : ∀ u, hermitianPairing (D.W (D.V 0 u)) (T u) =
      hermitianPairing (D.W (D.L u)) (T u) -
        ∑ i : Fin k, hermitianPairing (D.W (D.V i.succ (D.V i.succ u))) (T u) -
        hermitianPairing (D.W (realMultiplierOperator D.c u)) (T u) := fun u => by
    rw [hV0 u, map_sub, map_sub, H_sub_left, H_sub_left, map_sum, H_sum_left]
  simp_rw [e]
  exact (h.termB1.sub (SBound.sum fun i => h.termB3 hTs hTsc hP i)).sub h.termB2

/-- The full pairing bound: `|(Z u, T u)| ≤ K S(u)²`, with `Z = [X₀, W]`. -/
theorem termZ {Ts : Operator N} (hTs : HasHermitianAdjoint T Ts)
    (hTsc : OperatorClass (2 * D.α - 1) Ts) :
    SBound D (fun u => hermitianPairing (operatorComm (D.V 0) D.W u) (T u)) := by
  have hP := fun i : Fin k => h.termP hTsc i
  have e : ∀ u, hermitianPairing (operatorComm (D.V 0) D.W u) (T u) =
      hermitianPairing (D.V 0 (D.W u)) (T u) - hermitianPairing (D.W (D.V 0 u)) (T u) := fun u => by
    simp only [operatorComm, LinearMap.sub_apply, LinearMap.comp_apply]
    exact H_sub_left _ _ _
  simp_rw [e]
  exact (h.termA hTs hTsc hP).sub (h.termB hTs hTsc hP)

end DriftHyp
end Hormander.C
