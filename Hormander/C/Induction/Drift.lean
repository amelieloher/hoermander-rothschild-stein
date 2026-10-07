-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import Hormander.C.Induction.DriftB

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section
open MeasureTheory SchwartzMap
open scoped ComplexConjugate
namespace Hormander.C
open Hormander.B
variable {N : ℕ}

theorem drift_arith (K C6 kk a n w4 s2 σ E : ℝ) (hK : 0 ≤ K) (hC6 : 0 ≤ C6) (hk : 0 ≤ kk)
    (hE : E ≤ C6 * (a ^ 2 + n ^ 2)) (hcs : σ ^ 2 ≤ kk * E)
    (hS : s2 ≤ 4 * (a ^ 2 + n ^ 2 + w4 ^ 2 + σ ^ 2)) :
    K * s2 ≤ K * (4 * (1 + kk * C6)) * (a ^ 2 + n ^ 2 + w4 ^ 2) := by
  have h3 : σ ^ 2 ≤ kk * (C6 * (a ^ 2 + n ^ 2)) := hcs.trans (mul_le_mul_of_nonneg_left hE hk)
  have hmid : s2 ≤ 4 * (1 + kk * C6) * (a ^ 2 + n ^ 2 + w4 ^ 2) := by
    have h4 : 0 ≤ kk * C6 := mul_nonneg hk hC6
    have h5 : kk * (C6 * (a ^ 2 + n ^ 2)) ≤ kk * C6 * (a ^ 2 + n ^ 2 + w4 ^ 2) := by
      rw [← mul_assoc]
      exact mul_le_mul_of_nonneg_left (by nlinarith [sq_nonneg w4]) h4
    nlinarith [sq_nonneg a, sq_nonneg n, sq_nonneg w4]
  calc K * s2 ≤ K * (4 * (1 + kk * C6) * (a ^ 2 + n ^ 2 + w4 ^ 2)) :=
        mul_le_mul_of_nonneg_left hmid hK
    _ = _ := by ring

/-- The fourfold-loss drift recursion for every real Schwartz vector, under the closure
facts and horizontal recurrence hypotheses.
field `Y` and `0 < α < 1/4`. -/
theorem drift_recurrence_of_B10 (F : B10Facts N) {k : ℕ}
    (X : Fin (k + 1) → RealSchwartzVectorField N) (c : SchwartzMap (Carrier N) ℝ)
    (hH : HorizontalRecurrence X) : DriftRecurrence X c := by
  intro α hα hα4 Y
  set D : DriftData N k := ⟨X, c, Y, α⟩ with hD
  -- the operator `T = Λ^{2α-2} [X₀, Y]`
  set T : Operator N := (lambdaOperator (2 * α - 2)).comp (operatorComm (D.V 0) D.W) with hT
  have hZ : OperatorClass 1 (operatorComm (D.V 0) D.W) :=
    F.comm_vectorField 1 D.W (D.X 0) (F.vectorField_mem Y)
  have hTc : OperatorClass (2 * α - 1) T := by
    have := F.comp_mem _ _ _ _ (F.lambda_mem (2 * α - 2)) hZ
    have e : 2 * α - 2 + 1 = 2 * α - 1 := by ring
    rw [e] at this
    exact this
  obtain ⟨Ts, hTs, hTsc⟩ := F.class_adjoint hTc
  -- the recurrence at `δ = 2α` controls `[Xᵢ, Y] u`
  obtain ⟨C5, hC5, h5⟩ := hH (2 * α) (by linarith) (by linarith) Y
  have hU : ∀ i : Fin k, SLe D (fun u => sobolevNorm (2 * α - 1) (operatorComm (D.V i.succ) D.W u)) := by
    intro i
    refine ⟨Real.sqrt (3 * C5), by positivity, fun u => ?_⟩
    have hSn := D.S_nonneg u
    refine sqrt_bound (sobolevNorm_nonneg _ _) (by positivity) hSn ?_
    have e := h5 i.succ u
    have e2 : 2 * (2 * α) - 1 = 4 * α - 1 := by ring
    rw [e2] at e
    have e3 : 2 * α - 1 = 2 * α - 1 := rfl
    have ha := D.e_le_S i u
    have hb := D.w_le_S u
    have hc := D.n_le_S u
    have hq1 : normSq (vectorFieldOperator (X i.succ) u) ≤ D.S u ^ 2 := by
      rw [← sobolevNorm_zero_sq]; exact pow_le_pow_left₀ (sobolevNorm_nonneg _ _) ha 2
    have hq2 : sobolevNorm (4 * α - 1) (vectorFieldOperator Y u) ^ 2 ≤ D.S u ^ 2 :=
      pow_le_pow_left₀ (sobolevNorm_nonneg _ _) hb 2
    have hq3 : normSq u ≤ D.S u ^ 2 := by
      rw [← sobolevNorm_zero_sq]; exact pow_le_pow_left₀ (sobolevNorm_nonneg _ _) hc 2
    change sobolevNorm (2 * α - 1) (operatorComm (vectorFieldOperator (X i.succ)) (vectorFieldOperator Y) u) ^ 2 ≤ _
    refine e.trans ?_
    nlinarith [mul_le_mul_of_nonneg_left hq1 hC5.le, mul_le_mul_of_nonneg_left hq2 hC5.le,
      mul_le_mul_of_nonneg_left hq3 hC5.le]
  have hyp : DriftHyp D T :=
    { F := F, α_pos := hα, α_lt := hα4, T_mem := hTc, U_le := hU }
  obtain ⟨K, hK0, hK⟩ := hyp.termZ hTs hTsc
  obtain ⟨C6, hC6, hE⟩ := energy_bound X c
  refine ⟨4 * K * (1 + k * C6) + 1, by positivity, fun u => ?_⟩
  have hid := sobolevNorm_sq_eq_re_pairing (α - 1) (operatorComm (D.V 0) D.W u)
  have e2 : (2 : ℝ) * (α - 1) = 2 * α - 2 := by ring
  rw [e2] at hid
  have hTu : lambdaOperator (2 * α - 2) (operatorComm (D.V 0) D.W u) = T u := rfl
  rw [hTu] at hid
  have h1 : sobolevNorm (α - 1) (operatorComm (D.V 0) D.W u) ^ 2 ≤ K * D.S u ^ 2 := by
    rw [hid, H_re_symm]
    exact (Complex.re_le_norm _).trans (hK u)
  -- bound `S²`
  set a := sobolevNorm 0 (D.L u) with ha
  set n := sobolevNorm 0 u with hn
  set w4 := sobolevNorm (4 * α - 1) (vectorFieldOperator Y u) with hw4
  set e : Fin k → ℝ := fun i => sobolevNorm 0 (D.V i.succ u) with he
  have hE' : ∑ i : Fin k, e i ^ 2 ≤ C6 * (a ^ 2 + n ^ 2) := by
    have := hE u
    simp only [he, ha, hn, sobolevNorm_zero_sq]
    exact this
  have hcs : (∑ i : Fin k, e i) ^ 2 ≤ k * ∑ i : Fin k, e i ^ 2 := by
    have := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset (Fin k)) (fun _ => (1 : ℝ)) e
    simpa using this
  have ha0 : 0 ≤ a := sobolevNorm_nonneg _ _
  have hn0 : 0 ≤ n := sobolevNorm_nonneg _ _
  have hw0 : 0 ≤ w4 := sobolevNorm_nonneg _ _
  have hs0 : 0 ≤ ∑ i : Fin k, e i := Finset.sum_nonneg fun i _ => sobolevNorm_nonneg _ _
  have hS : D.S u ^ 2 ≤ 4 * (a ^ 2 + n ^ 2 + w4 ^ 2 + (∑ i : Fin k, e i) ^ 2) := by
    change (a + n + w4 + ∑ i : Fin k, e i) ^ 2 ≤ _
    nlinarith [sq_nonneg (a - n), sq_nonneg (a - w4), sq_nonneg (a - ∑ i : Fin k, e i),
      sq_nonneg (n - w4), sq_nonneg (n - ∑ i : Fin k, e i), sq_nonneg (w4 - ∑ i : Fin k, e i)]
  have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have hfin : sobolevNorm (α - 1) (operatorComm (D.V 0) D.W u) ^ 2 ≤
      K * (4 * (1 + k * C6)) * (a ^ 2 + n ^ 2 + w4 ^ 2) :=
    h1.trans (drift_arith K C6 k a n w4 (D.S u ^ 2) (∑ i : Fin k, e i) (∑ i : Fin k, e i ^ 2)
      hK0 hC6.le hk0 hE' hcs hS)
  have hsq : a ^ 2 + n ^ 2 + w4 ^ 2 = normSq (diffusionOperator X c u) + w4 ^ 2 + normSq u := by
    rw [ha, hn, sobolevNorm_zero_sq, sobolevNorm_zero_sq]
    change normSq (diffusionOperator X c u) + normSq u + w4 ^ 2 = _
    ring
  have hpos : 0 ≤ a ^ 2 + n ^ 2 + w4 ^ 2 := by
    have h1 := sq_nonneg a; have h2 := sq_nonneg n; have h3 := sq_nonneg w4; linarith
  have hcoef : K * (4 * (1 + k * C6)) * (a ^ 2 + n ^ 2 + w4 ^ 2) ≤
      (4 * K * (1 + k * C6) + 1) * (a ^ 2 + n ^ 2 + w4 ^ 2) := by
    have hh : (4 * K * (1 + k * C6) + 1) * (a ^ 2 + n ^ 2 + w4 ^ 2) -
        K * (4 * (1 + k * C6)) * (a ^ 2 + n ^ 2 + w4 ^ 2) = a ^ 2 + n ^ 2 + w4 ^ 2 := by ring
    linarith
  calc sobolevNorm (α - 1) (operatorComm (D.V 0) D.W u) ^ 2 ≤ _ := hfin
    _ ≤ (4 * K * (1 + k * C6) + 1) * (a ^ 2 + n ^ 2 + w4 ^ 2) := hcoef
    _ = _ := by rw [hsq]

/-- with the gain `ε_s = 2/4^s`: one constant for all words of ordinary length `ℓ ≤ s`. -/
theorem drift_word_estimate_gain_of_B10 (F : B10Facts N) {k : ℕ}
    (X : Fin (k + 1) → RealSchwartzVectorField N) (c : SchwartzMap (Carrier N) ℝ)
    (hH : HorizontalRecurrence X) (s : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ ℓ : ℕ, 1 ≤ ℓ → ℓ ≤ s → WordEstimate X c ℓ (2 / 4 ^ s) C :=
  word_estimate_gain X c hH (drift_recurrence_of_B10 F X c hH)
    (fun _ hα => base_drift_of_B10 F X c hα) s

end Hormander.C
