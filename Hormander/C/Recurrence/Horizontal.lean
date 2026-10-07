-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import Hormander.C.Induction.Duality
import all Mathlib.Basic.Real.Basic

@[expose] public section

noncomputable section

namespace Hormander.C
open Hormander.B
variable {N : ℕ}

/-- The three combined operators needed for integration by parts, under the stated hypotheses. -/
theorem horizontal_order_ledger_of_B10 (F : B10Facts N)
    (X Y : RealSchwartzVectorField N) (δ : ℝ) :
    let Z := operatorComm (vectorFieldOperator X) (vectorFieldOperator Y)
    let P := (lambdaOperator (2 * δ - 2)).comp Z
    OperatorClass (2 * δ - 1) P ∧
    OperatorClass (2 * δ - 1)
      (-operatorComm (vectorFieldOperator X) P + (realMultiplierOperator (negDiv X)).comp P) ∧
    OperatorClass (2 * δ - 1)
      (-operatorComm (vectorFieldOperator Y) P + (realMultiplierOperator (negDiv Y)).comp P) := by
  dsimp
  have hZ := F.comm_vectorField 1 _ X (F.vectorField_mem Y)
  have hP := F.comp_mem (2 * δ - 2) 1 _ _ (F.lambda_mem _) hZ
  have he : 2 * δ - 2 + 1 = 2 * δ - 1 := by ring
  rw [he] at hP
  have hR (V : RealSchwartzVectorField N) : OperatorClass (2 * δ - 1)
      (-operatorComm (vectorFieldOperator V)
          ((lambdaOperator (2 * δ - 2)).comp
            (operatorComm (vectorFieldOperator X) (vectorFieldOperator Y))) +
        (realMultiplierOperator (negDiv V)).comp
          ((lambdaOperator (2 * δ - 2)).comp
            (operatorComm (vectorFieldOperator X) (vectorFieldOperator Y)))) := by
    apply F.add_mem
    · simpa using (F.smul_mem _ (-1) _ (F.comm_vectorField _ _ V hP))
    · simpa using (F.comp_mem 0 _ _ _ (F.multiplier_mem _) hP)
  exact ⟨hP, hR X, hR Y⟩

/-- Move a field across `P`, with its divergence term and commutator explicit. -/
theorem horizontal_transfer (X : RealSchwartzVectorField N) (P : Operator N)
    (a u : TestFunction N) :
    hermitianPairing (vectorFieldOperator X a) (P u) =
      -hermitianPairing a (P (vectorFieldOperator X u)) +
      hermitianPairing a
        ((-operatorComm (vectorFieldOperator X) P +
          (realMultiplierOperator (negDiv X)).comp P) u) := by
  rw [H_vectorField_left]
  have he : vectorFieldOperator X (P u) =
      P (vectorFieldOperator X u) + operatorComm (vectorFieldOperator X) P u := by
    simp [operatorComm]
  rw [he, H_add_right]
  simp only [LinearMap.add_apply, LinearMap.neg_apply, LinearMap.comp_apply,
    H_add_right, H_neg_right]
  ring

/-- Horizontal recurrence, under the stated hypotheses. -/
theorem horizontal_recurrence_single_of_B10 (F : B10Facts N)
    (X Y : RealSchwartzVectorField N) (δ : ℝ) (_hδ : 0 < δ) (hδ : δ ≤ 1 / 2) :
    ∃ C : ℝ, 0 < C ∧ ∀ u : TestFunction N,
      sobolevNorm (δ - 1) (operatorComm (vectorFieldOperator X) (vectorFieldOperator Y) u) ^ 2 ≤
        C * (sobolevNorm 0 (vectorFieldOperator X u) ^ 2 +
          sobolevNorm (2 * δ - 1) (vectorFieldOperator Y u) ^ 2 + sobolevNorm 0 u ^ 2) := by
  let V := vectorFieldOperator X
  let W := vectorFieldOperator Y
  let Z := operatorComm V W
  let τ := 2 * δ - 1
  let P := (lambdaOperator (2 * δ - 2)).comp Z
  let R := -operatorComm V P + (realMultiplierOperator (negDiv X)).comp P
  let S := -operatorComm W P + (realMultiplierOperator (negDiv Y)).comp P
  obtain ⟨hP, hR, hS⟩ := horizontal_order_ledger_of_B10 F X Y δ
  change OperatorClass τ P at hP
  change OperatorClass τ R at hR
  change OperatorClass τ S at hS
  obtain ⟨A, hA⟩ := hP.hasOrder' (-τ)
  obtain ⟨B, hB⟩ := hR.hasOrder' (-τ)
  obtain ⟨D, hD⟩ := hP.hasOrder' 0
  obtain ⟨E, hE⟩ := hS.hasOrder' 0
  simp only [neg_add_cancel] at hA hB
  simp only [zero_add] at hD hE
  let K : ℝ := A + B + D + E + 1
  have hK : 0 < K := by dsimp [K]; positivity
  refine ⟨3 * K, by positivity, fun u => ?_⟩
  let x := sobolevNorm 0 (V u)
  let y := sobolevNorm τ (W u)
  let n := sobolevNorm 0 u
  have hx : 0 ≤ x := sobolevNorm_nonneg _ _
  have hy : 0 ≤ y := sobolevNorm_nonneg _ _
  have hn : 0 ≤ n := sobolevNorm_nonneg _ _
  have hτ : τ ≤ 0 := by dsimp [τ]; linarith
  have hSu : sobolevNorm 0 (S u) ≤ E * n :=
    (hE u).trans (mul_le_mul_of_nonneg_left (sobolevNorm_mono hτ u) E.2)
  have hp1 : ‖hermitianPairing (W u) (P (V u))‖ ≤ A * (y * x) := by
    refine (H_duality _ _ τ).trans ?_
    have := mul_le_mul_of_nonneg_left (hA (V u)) hy
    dsimp [x, y] at *
    nlinarith
  have hp2 : ‖hermitianPairing (W u) (R u)‖ ≤ B * (y * n) := by
    refine (H_duality _ _ τ).trans ?_
    have := mul_le_mul_of_nonneg_left (hB u) hy
    dsimp [y, n] at *
    nlinarith
  have hp3 : ‖hermitianPairing (V u) (P (W u))‖ ≤ D * (x * y) := by
    refine (H_duality _ _ 0).trans ?_
    simp only [neg_zero]
    have := mul_le_mul_of_nonneg_left (hD (W u)) hx
    dsimp [x, y] at *
    nlinarith
  have hp4 : ‖hermitianPairing (V u) (S u)‖ ≤ E * (x * n) := by
    refine (H_duality _ _ 0).trans ?_
    simp only [neg_zero]
    have := mul_le_mul_of_nonneg_left hSu hx
    dsimp [x, n] at *
    nlinarith
  have hid : hermitianPairing (Z u) (P u) =
      (-hermitianPairing (W u) (P (V u)) + hermitianPairing (W u) (R u)) -
      (-hermitianPairing (V u) (P (W u)) + hermitianPairing (V u) (S u)) := by
    change hermitianPairing (V (W u) - W (V u)) (P u) = _
    rw [sub_eq_add_neg, H_add_left]
    have hneg : ∀ a b : TestFunction N, hermitianPairing (-a) b = -hermitianPairing a b := by
      intro a b
      rw [H_conj_symm, H_neg_right, map_neg, ← H_conj_symm]
    rw [hneg]
    change hermitianPairing (vectorFieldOperator X (W u)) (P u) +
      -hermitianPairing (vectorFieldOperator Y (V u)) (P u) = _
    rw [horizontal_transfer X P (W u) u, horizontal_transfer Y P (V u) u]
    change (-hermitianPairing (W u) (P (V u)) + hermitianPairing (W u) (R u)) +
      -(-hermitianPairing (V u) (P (W u)) + hermitianPairing (V u) (S u)) = _
    ring
  have hnorm : ‖hermitianPairing (Z u) (P u)‖ ≤
      A * (y * x) + B * (y * n) + D * (x * y) + E * (x * n) := by
    rw [hid]
    refine (norm_sub_le _ _).trans ?_
    have h1 := norm_add_le (-hermitianPairing (W u) (P (V u))) (hermitianPairing (W u) (R u))
    have h2 := norm_add_le (-hermitianPairing (V u) (P (W u))) (hermitianPairing (V u) (S u))
    simp only [norm_neg] at h1 h2
    linarith
  have hidnorm : sobolevNorm (δ - 1) (Z u) ^ 2 = (hermitianPairing (Z u) (P u)).re := by
    rw [sobolevNorm_sq_eq_re_pairing, H_re_symm]
    have he : 2 * (δ - 1) = 2 * δ - 2 := by ring
    rw [he]
    rfl
  have ha := A.2
  have hb := B.2
  have hd := D.2
  have he := E.2
  have hbound := le_trans (Complex.re_le_norm _) hnorm
  rw [← hidnorm] at hbound
  have hxy : x * y ≤ (x ^ 2 + y ^ 2 + n ^ 2) := by nlinarith [sq_nonneg (x - y), sq_nonneg n]
  have hyn : y * n ≤ (x ^ 2 + y ^ 2 + n ^ 2) := by nlinarith [sq_nonneg (y - n), sq_nonneg x]
  have hxn : x * n ≤ (x ^ 2 + y ^ 2 + n ^ 2) := by nlinarith [sq_nonneg (x - n), sq_nonneg y]
  have hsum : A * (y * x) + B * (y * n) + D * (x * y) + E * (x * n) ≤
      ((A : ℝ) + (B : ℝ) + (D : ℝ) + (E : ℝ)) * (x ^ 2 + y ^ 2 + n ^ 2) := by
    have h1 := mul_le_mul_of_nonneg_left hxy ha
    have h2 := mul_le_mul_of_nonneg_left hyn hb
    have h3 := mul_le_mul_of_nonneg_left hxy hd
    have h4 := mul_le_mul_of_nonneg_left hxn he
    rw [mul_comm x y] at h1
    have ht := add_le_add (add_le_add (add_le_add h1 h2) h3) h4
    have hinst : Real.instPreorder.toLE = Real.instLE := rfl
    rw [hinst] at ht
    simp only [mul_comm x y, ← add_mul] at ht ⊢
    convert! ht using 1
  change sobolevNorm (δ - 1) (Z u) ^ 2 ≤ 3 * K * (x ^ 2 + y ^ 2 + n ^ 2)
  have hnonneg : 0 ≤ x ^ 2 + y ^ 2 + n ^ 2 := by positivity
  exact (hbound.trans hsum).trans (mul_le_mul_of_nonneg_right (by dsimp [K]; linarith) hnonneg)

/-- The horizontal recurrence holds uniformly over the fields. -/
theorem horizontal_recurrence_of_B10 {k : ℕ} (F : B10Facts N)
    (X : Fin (k + 1) → RealSchwartzVectorField N) : HorizontalRecurrence X := by
  intro δ hδpos hδ Y
  have hsingle := fun j : Fin (k + 1) =>
    horizontal_recurrence_single_of_B10 F (X j) Y δ hδpos hδ
  choose C hC hbound using hsingle
  refine ⟨1 + ∑ j, C j, ?_, fun j u => ?_⟩
  · have := Finset.sum_nonneg (fun j (_ : j ∈ Finset.univ) => (hC j).le)
    linarith
  · have hj : C j ≤ ∑ i, C i :=
      Finset.single_le_sum (fun i _ => (hC i).le) (Finset.mem_univ j)
    have hn : 0 ≤ sobolevNorm 0 (vectorFieldOperator (X j) u) ^ 2 +
        sobolevNorm (2 * δ - 1) (vectorFieldOperator Y u) ^ 2 + sobolevNorm 0 u ^ 2 := by
      positivity
    have hb := (hbound j u).trans
      (mul_le_mul_of_nonneg_right (show C j ≤ 1 + ∑ i, C i by linarith) hn)
    simpa only [sobolevNorm_zero_sq] using hb

end Hormander.C
