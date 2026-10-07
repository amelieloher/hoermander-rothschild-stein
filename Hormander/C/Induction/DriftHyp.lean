-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import Hormander.C.Induction.DriftPairing

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section
open MeasureTheory SchwartzMap
open scoped ComplexConjugate
namespace Hormander.C
open Hormander.B
variable {N k : ℕ} {D : DriftData N k}

/-- The hypotheses of the drift step: the closure facts, `0 < α < 1/4`, an operator `T` of
class `𝓞^{2α-1}`, and the horizontal recurrence at parameter `2α` for the fields `[Xᵢ, Y]`. -/
structure DriftHyp (D : DriftData N k) (T : Operator N) : Prop where
  F : B10Facts N
  α_pos : 0 < D.α
  α_lt : D.α < 1 / 4
  T_mem : OperatorClass (2 * D.α - 1) T
  U_le : ∀ i : Fin k, SLe D (fun u => sobolevNorm (2 * D.α - 1) (operatorComm (D.V i.succ) D.W u))

namespace DriftHyp
variable {T : Operator N} (h : DriftHyp D T)
include h

theorem sLu : SLe D (fun u => sobolevNorm 0 (D.L u)) := SLe.of_le D.a_le_S
theorem sn : SLe D (fun u => sobolevNorm 0 u) := SLe.of_le D.n_le_S
theorem sn_nonpos {s : ℝ} (hs : s ≤ 0) : SLe D (fun u => sobolevNorm s u) :=
  (sn h).mono fun u => sobolevNorm_mono hs u
theorem sWτ : SLe D (fun u => sobolevNorm (2 * D.α - 1) (D.W u)) :=
  SLe.of_le (D.wτ_le_S h.α_pos.le)
theorem sW4 : SLe D (fun u => sobolevNorm (4 * D.α - 1) (D.W u)) := SLe.of_le D.w_le_S
theorem sV (i : Fin k) : SLe D (fun u => sobolevNorm 0 (D.V i.succ u)) := SLe.of_le (D.e_le_S i)

theorem τ_neg : 2 * D.α - 1 ≤ 0 := by linarith [h.α_lt]

end DriftHyp

/-- `(★)`: transferring the drift field across the pairing. -/
theorem star_identity (D : DriftData N k) (a b : TestFunction N) :
    hermitianPairing (D.V 0 a) b =
      -hermitianPairing a (D.L b) + ∑ i : Fin k, hermitianPairing a (D.V i.succ (D.V i.succ b)) +
        hermitianPairing a (realMultiplierOperator D.c b) +
        hermitianPairing a (realMultiplierOperator (negDiv (D.X 0)) b) := by
  have h1 := H_vectorField_left (D.X 0) a b
  have hL : D.L b = (∑ i : Fin k, D.V i.succ (D.V i.succ b)) + D.V 0 b + realMultiplierOperator D.c b := by
    unfold DriftData.L diffusionOperator DriftData.V
    simp only [LinearMap.add_apply, LinearMap.sum_apply, LinearMap.comp_apply]
  have h2 : D.V 0 b = D.L b - (∑ i : Fin k, D.V i.succ (D.V i.succ b)) - realMultiplierOperator D.c b := by
    rw [hL]; abel
  have h3 : hermitianPairing a (D.V 0 b) = hermitianPairing a (D.L b) -
      ∑ i : Fin k, hermitianPairing a (D.V i.succ (D.V i.succ b)) -
      hermitianPairing a (realMultiplierOperator D.c b) := by
    rw [h2]
    have hsub : ∀ x y z : TestFunction N, hermitianPairing a (x - y - z) =
        hermitianPairing a x - hermitianPairing a y - hermitianPairing a z := by
      intro x y z
      rw [sub_eq_add_neg, sub_eq_add_neg, H_add_right, H_add_right, H_neg_right, H_neg_right]; ring
    rw [hsub]
    congr 2
    -- H(a, Σ) = Σ H(a, ·)
    have : ∀ (I : Finset (Fin k)) (f : Fin k → TestFunction N),
        hermitianPairing a (∑ i ∈ I, f i) = ∑ i ∈ I, hermitianPairing a (f i) := by
      intro I f
      classical
      induction I using Finset.induction_on with
      | empty => simp [hermitianPairing]
      | insert i I hi ih => rw [Finset.sum_insert hi, Finset.sum_insert hi, H_add_right, ih]
    exact this _ _
  have h1' : hermitianPairing (D.V 0 a) b = -hermitianPairing a (vectorFieldOperator (D.X 0) b) +
      hermitianPairing a (realMultiplierOperator (negDiv (D.X 0)) b) := h1
  rw [h1']
  change -hermitianPairing a (D.V 0 b) + _ = _
  rw [h3]; ring

theorem H_sum_right {ι : Type*} (I : Finset ι) (a : TestFunction N) (f : ι → TestFunction N) :
    hermitianPairing a (∑ i ∈ I, f i) = ∑ i ∈ I, hermitianPairing a (f i) := by
  classical
  induction I using Finset.induction_on with
  | empty => simp [hermitianPairing]
  | insert i I hi ih => rw [Finset.sum_insert hi, Finset.sum_insert hi, H_add_right, ih]

end Hormander.C
