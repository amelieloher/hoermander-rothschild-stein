-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import Hormander.C.Induction.DriftHyp
public import Hormander.C.Induction.Decomposition

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section
open MeasureTheory SchwartzMap
open scoped ComplexConjugate
namespace Hormander.C
open Hormander.B
variable {N k : ℕ} {D : DriftData N k} {T : Operator N}

/-- `V(Su) = S(Vu) + [V,S]u`. -/
theorem apply_comm_split (V Sop : Operator N) (u : TestFunction N) :
    V (Sop u) = Sop (V u) + operatorComm V Sop u := by
  simp only [operatorComm, LinearMap.sub_apply, LinearMap.comp_apply]; abel

theorem H_adjoint_right {T Ts : Operator N} (hT : HasHermitianAdjoint T Ts) (a b : TestFunction N) :
    hermitianPairing a (T b) = hermitianPairing (Ts a) b := by
  rw [H_conj_symm a, hT b a, ← H_conj_symm]

namespace DriftHyp
variable (h : DriftHyp D T)
include h

/-- Class helpers. -/
theorem cls_mulT (g : SchwartzMap (Carrier N) ℝ) :
    OperatorClass (2 * D.α - 1) ((realMultiplierOperator g).comp T) := by
  simpa using h.F.comp_mem 0 _ _ _ (h.F.multiplier_mem g) h.T_mem

theorem cls_commV (j : Fin (k + 1)) :
    OperatorClass (2 * D.α - 1) (operatorComm (D.V j) T) :=
  h.F.comm_vectorField _ T (D.X j) h.T_mem

theorem cls_commW :
    OperatorClass (2 * D.α - 1) (operatorComm D.W T) :=
  h.F.comm_vectorField _ T D.Y h.T_mem

theorem cls_commV_commV (j : Fin (k + 1)) :
    OperatorClass (2 * D.α - 1) (operatorComm (D.V j) (operatorComm (D.V j) T)) :=
  h.F.comm_vectorField _ _ (D.X j) (h.cls_commV j)

theorem cls_commV_mulT (j : Fin (k + 1)) (g : SchwartzMap (Carrier N) ℝ) :
    OperatorClass (2 * D.α - 1) (operatorComm (D.V j) ((realMultiplierOperator g).comp T)) :=
  h.F.comm_vectorField _ _ (D.X j) (h.cls_mulT g)

theorem cls_mulcommV (j : Fin (k + 1)) (g : SchwartzMap (Carrier N) ℝ) :
    OperatorClass (2 * D.α - 1) ((realMultiplierOperator g).comp (operatorComm (D.V j) T)) := by
  simpa using h.F.comp_mem 0 _ _ _ (h.F.multiplier_mem g) (h.cls_commV j)

/-- [A1] `(Wu, L T u)`. -/
theorem termA1 : SBound D (fun u => hermitianPairing (D.W u) (D.L (T u))) := by
  obtain ⟨Tj, T0, hTj, hT0, hdec⟩ := commutator_left_decomposition_of_B10 h.F D.X D.c h.T_mem
  have e : ∀ u, D.L (T u) = T (D.L u) + (∑ j : Fin k, (Tj j) (D.V j.succ u)) + T0 u := by
    intro u
    have := LinearMap.congr_fun hdec u
    simp only [operatorComm, LinearMap.sub_apply, LinearMap.add_apply, LinearMap.comp_apply,
      LinearMap.sum_apply] at this
    have this' : D.L (T u) - T (D.L u) = ∑ j : Fin k, (Tj j) (D.V j.succ u) + T0 u := this
    rw [sub_eq_iff_eq_add] at this'
    rw [this']; abel
  have hW := h.sWτ
  have h1 : SBound D (fun u => hermitianPairing (D.W u) (T (D.L u))) :=
    SBound.right' h.F h.T_mem (2 * D.α - 1) 0 (by ring) hW h.sLu
  have h2 : ∀ j : Fin k, SBound D (fun u => hermitianPairing (D.W u) ((Tj j) (D.V j.succ u))) :=
    fun j => SBound.right' h.F (hTj j) (2 * D.α - 1) 0 (by ring) hW (h.sV j)
  have h3 : SBound D (fun u => hermitianPairing (D.W u) (T0 u)) :=
    SBound.right' h.F hT0 (2 * D.α - 1) 0 (by ring) hW h.sn (B := fun u => u)
  have h4 : SBound D (fun u => hermitianPairing (D.W u) (∑ j : Fin k, (Tj j) (D.V j.succ u))) := by
    simp_rw [H_sum_right]
    exact SBound.sum h2
  have : (fun u => hermitianPairing (D.W u) (D.L (T u))) = fun u =>
      hermitianPairing (D.W u) (T (D.L u)) + hermitianPairing (D.W u)
        (∑ j : Fin k, (Tj j) (D.V j.succ u)) + hermitianPairing (D.W u) (T0 u) := by
    funext u
    rw [e u, H_add_right, H_add_right]
  rw [this]
  exact (h1.add h4).add h3

theorem termA3 : SBound D (fun u => hermitianPairing (D.W u)
    (realMultiplierOperator D.c (T u))) :=
  SBound.right' h.F (h.cls_mulT D.c) (2 * D.α - 1) 0 (by ring) h.sWτ h.sn (B := fun u => u)

theorem termA4 : SBound D (fun u => hermitianPairing (D.W u)
    (realMultiplierOperator (negDiv (D.X 0)) (T u))) :=
  SBound.right' h.F (h.cls_mulT _) (2 * D.α - 1) 0 (by ring) h.sWτ h.sn (B := fun u => u)

/-- The `g`-term in `A₂`. -/
theorem termA2b (i : Fin k) : SBound D (fun u => hermitianPairing
    (realMultiplierOperator (negDiv (D.X i.succ)) (D.W u)) (D.V i.succ (T u))) := by
  have e : ∀ u, hermitianPairing (realMultiplierOperator (negDiv (D.X i.succ)) (D.W u)) (D.V i.succ (T u)) =
      hermitianPairing (D.W u) ((realMultiplierOperator (negDiv (D.X i.succ))).comp T (D.V i.succ u)) +
      hermitianPairing (D.W u) ((realMultiplierOperator (negDiv (D.X i.succ))).comp
        (operatorComm (D.V i.succ) T) u) := fun u => by
    rw [H_realMultiplier_left, apply_comm_split (D.V i.succ) T u]
    simp only [LinearMap.comp_apply, map_add, H_add_right]
  simp_rw [e]
  exact (SBound.right' h.F (h.cls_mulT _) (2 * D.α - 1) 0 (by ring) h.sWτ (h.sV i)
    (B := fun u => D.V i.succ u)).add
    (SBound.right' h.F (h.cls_mulcommV _ _) (2 * D.α - 1) 0 (by ring) h.sWτ h.sn (B := fun u => u))

theorem termD2 (i : Fin k) : SBound D (fun u => hermitianPairing (D.V i.succ (D.W u))
    (operatorComm (D.V i.succ) T u)) := by
  have e : ∀ u, hermitianPairing (D.V i.succ (D.W u)) (operatorComm (D.V i.succ) T u) =
      -(hermitianPairing (D.W u) ((operatorComm (D.V i.succ) T) (D.V i.succ u)) +
        hermitianPairing (D.W u) (operatorComm (D.V i.succ) (operatorComm (D.V i.succ) T) u)) +
      hermitianPairing (D.W u) ((realMultiplierOperator (negDiv (D.X i.succ))).comp
        (operatorComm (D.V i.succ) T) u) := fun u => by
    have h1 := H_vectorField_left (D.X i.succ) (D.W u) (operatorComm (D.V i.succ) T u)
    have h2 := apply_comm_split (D.V i.succ) (operatorComm (D.V i.succ) T) u
    change hermitianPairing (D.V i.succ (D.W u)) _ = _ at h1
    rw [h1]
    change -hermitianPairing (D.W u) (D.V i.succ (operatorComm (D.V i.succ) T u)) + _ = _
    rw [h2, H_add_right]
    rfl
  simp_rw [e]
  refine SBound.add (SBound.neg (SBound.add ?_ ?_)) ?_
  · exact SBound.right' h.F (h.cls_commV _) (2 * D.α - 1) 0 (by ring) h.sWτ (h.sV i)
      (B := fun u => D.V i.succ u)
  · exact SBound.right' h.F (h.cls_commV_commV _) (2 * D.α - 1) 0 (by ring) h.sWτ h.sn (B := fun u => u)
  · exact SBound.right' h.F (h.cls_mulcommV _ _) (2 * D.α - 1) 0 (by ring) h.sWτ h.sn (B := fun u => u)

theorem termD1 {Ts : Operator N} (hTs : HasHermitianAdjoint T Ts)
    (hTsc : OperatorClass (2 * D.α - 1) Ts)
    (hP : ∀ i : Fin k, SBound D (fun u => hermitianPairing (D.V i.succ (Ts (D.W u))) (D.V i.succ u)))
    (i : Fin k) :
    SBound D (fun u => hermitianPairing (D.V i.succ (D.W u)) (T (D.V i.succ u))) := by
  have e : ∀ u, hermitianPairing (D.V i.succ (D.W u)) (T (D.V i.succ u)) =
      hermitianPairing (D.V i.succ (Ts (D.W u))) (D.V i.succ u) -
        hermitianPairing (operatorComm (D.V i.succ) Ts (D.W u)) (D.V i.succ u) := fun u => by
    rw [H_adjoint_right hTs]
    have h2 := apply_comm_split (D.V i.succ) Ts (D.W u)
    have : Ts (D.V i.succ (D.W u)) = D.V i.succ (Ts (D.W u)) - operatorComm (D.V i.succ) Ts (D.W u) := by
      rw [h2]; abel
    rw [this]
    have hs : ∀ x y z : TestFunction N, hermitianPairing (x - y) z =
        hermitianPairing x z - hermitianPairing y z := fun x y z => H_sub_left x y z
    exact hs _ _ _
  simp_rw [e]
  refine SBound.sub (hP i) ?_
  exact SBound.left' h.F (h.F.comm_vectorField _ Ts (D.X i.succ) hTsc) 0 (2 * D.α - 1) (by ring)
    h.sWτ (h.sV i) (B := fun u => D.V i.succ u)

theorem termDi {Ts : Operator N} (hTs : HasHermitianAdjoint T Ts)
    (hTsc : OperatorClass (2 * D.α - 1) Ts)
    (hP : ∀ i : Fin k, SBound D (fun u => hermitianPairing (D.V i.succ (Ts (D.W u))) (D.V i.succ u)))
    (i : Fin k) :
    SBound D (fun u => hermitianPairing (D.V i.succ (D.W u)) (D.V i.succ (T u))) := by
  have e : ∀ u, hermitianPairing (D.V i.succ (D.W u)) (D.V i.succ (T u)) =
      hermitianPairing (D.V i.succ (D.W u)) (T (D.V i.succ u)) +
        hermitianPairing (D.V i.succ (D.W u)) (operatorComm (D.V i.succ) T u) := fun u => by
    rw [apply_comm_split (D.V i.succ) T u, H_add_right]
  simp_rw [e]
  exact (h.termD1 hTs hTsc hP i).add (h.termD2 i)

theorem termA2 {Ts : Operator N} (hTs : HasHermitianAdjoint T Ts)
    (hTsc : OperatorClass (2 * D.α - 1) Ts)
    (hP : ∀ i : Fin k, SBound D (fun u => hermitianPairing (D.V i.succ (Ts (D.W u))) (D.V i.succ u))) :
    SBound D (fun u => ∑ i : Fin k, hermitianPairing (D.W u) (D.V i.succ (D.V i.succ (T u)))) := by
  refine SBound.sum fun i => ?_
  have e : ∀ u, hermitianPairing (D.W u) (D.V i.succ (D.V i.succ (T u))) =
      -hermitianPairing (D.V i.succ (D.W u)) (D.V i.succ (T u)) +
        hermitianPairing (realMultiplierOperator (negDiv (D.X i.succ)) (D.W u)) (D.V i.succ (T u)) :=
    fun u => H_vectorField_right (D.X i.succ) (D.W u) (D.V i.succ (T u))
  simp_rw [e]
  exact (h.termDi hTs hTsc hP i).neg.add (h.termA2b i)

/-- The `A` side: `(X₀ W u, T u)`. -/
theorem termA {Ts : Operator N} (hTs : HasHermitianAdjoint T Ts)
    (hTsc : OperatorClass (2 * D.α - 1) Ts)
    (hP : ∀ i : Fin k, SBound D (fun u => hermitianPairing (D.V i.succ (Ts (D.W u))) (D.V i.succ u))) :
    SBound D (fun u => hermitianPairing (D.V 0 (D.W u)) (T u)) := by
  have e : ∀ u, hermitianPairing (D.V 0 (D.W u)) (T u) =
      -hermitianPairing (D.W u) (D.L (T u)) +
        (∑ i : Fin k, hermitianPairing (D.W u) (D.V i.succ (D.V i.succ (T u)))) +
        hermitianPairing (D.W u) (realMultiplierOperator D.c (T u)) +
        hermitianPairing (D.W u) (realMultiplierOperator (negDiv (D.X 0)) (T u)) := fun u => by
    exact star_identity D (D.W u) (T u)
  simp_rw [e]
  exact (((h.termA1.neg).add (h.termA2 hTs hTsc hP)).add h.termA3).add h.termA4

end DriftHyp
end Hormander.C
