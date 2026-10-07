-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import Hormander.C.Induction.Facts
public import Hormander.B.Calculus.OrderClassTranspose
public import Hormander.B.Calculus.OrderClassProducts
public import Hormander.B.Nested.NormalForm
public import Hormander.B.Differential

@[expose] public section

noncomputable section

namespace Hormander.B

variable {N : ℕ}

/-- Iterated commutators of a differential operator lose one differential degree
for each multiplier generator, and vanish after more losses than its degree. -/
theorem IsDiffOp.iterated_commutator_degree {p : ℕ} {T : Operator N}
    (hT : IsDiffOp p T) (ys : List (OperatorGenerator N)) :
    IsDiffOp (p - multiplierCount ys) (iteratedCommutator ys T) ∧
    (multiplierCount ys > p → iteratedCommutator ys T = 0) := by
  induction ys with
  | nil =>
      constructor
      · simpa [multiplierCount, iteratedCommutator] using hT
      · intro h
        simp [multiplierCount] at h
  | cons Y ys ih =>
      obtain ⟨hTail, hTailZero⟩ := ih
      cases Y with
      | vectorField X =>
          have hX := isDiffOp_vectorFieldOperator X
          have hcomm := hX.comm hTail
          have hc : multiplierCount (.vectorField X :: ys) = multiplierCount ys := by
            rw [multiplierCount_cons_local]
            simp [OperatorGenerator.isMultiplier]
          constructor
          · change IsDiffOp (p - multiplierCount (.vectorField X :: ys))
              (operatorComm (vectorFieldOperator X) (iteratedCommutator ys T))
            simpa [hc] using hcomm
          · intro hcount
            have hzero := hTailZero (by omega)
            simp [iteratedCommutator, OperatorGenerator.toOperator, hzero, operatorComm]
      | multiplier g =>
          let M := realMultiplierOperator g
          have hM : IsDiffOp 0 M := by
            simpa [M, realMultiplierOperator] using
              (IsDiffOp.mult 0 (complexifyRealSchwartz g))
          have hc : multiplierCount (.multiplier g :: ys) = multiplierCount ys + 1 := by
            rw [multiplierCount_cons_local]
            simp [OperatorGenerator.isMultiplier]
            omega
          have hd : p - multiplierCount ys = 0 ∨ 0 < p - multiplierCount ys :=
            Nat.eq_zero_or_pos _
          constructor
          · by_cases hz : p - multiplierCount ys = 0
            · have hcomm0 : operatorComm M (iteratedCommutator ys T) = 0 := by
                have htail0 : IsDiffOp 0 (iteratedCommutator ys T) := by simpa [hz] using hTail
                exact hM.comm_zero htail0
              change IsDiffOp (p - multiplierCount (.multiplier g :: ys))
                (operatorComm M (iteratedCommutator ys T))
              rw [hcomm0]
              have horder : p - multiplierCount (.multiplier g :: ys) = 0 := by
                rw [hc]
                omega
              rw [horder]
              exact isDiffOp_zero 0
            · have hcomm := hM.comm hTail
              change IsDiffOp (p - multiplierCount (.multiplier g :: ys))
                (operatorComm M (iteratedCommutator ys T))
              convert hcomm using 1
              simp [hc]
              omega
          · intro hcount
            by_cases htailmore : multiplierCount ys > p
            · have hzero := hTailZero htailmore
              simp [iteratedCommutator, OperatorGenerator.toOperator, hzero, operatorComm]
            · have heq : multiplierCount ys = p := by rw [hc] at hcount; omega
              have htail0 : IsDiffOp 0 (iteratedCommutator ys T) := by
                have : p - multiplierCount ys = 0 := by omega
                simpa [this] using hTail
              have hcomm0 : operatorComm M (iteratedCommutator ys T) = 0 :=
                hM.comm_zero htail0
              change operatorComm (realMultiplierOperator g)
                (iteratedCommutator ys T) = 0
              simpa [M] using hcomm0

private theorem iterated_diffOp_hasOrder {p : ℕ} {T : Operator N}
    (hT : IsDiffOp p T) (ys : List (OperatorGenerator N)) :
    HasOrder ((p : ℝ) - (multiplierCount ys : ℝ)) (iteratedCommutator ys T) := by
  obtain ⟨hdegree, hzero⟩ := hT.iterated_commutator_degree ys
  by_cases hc : multiplierCount ys ≤ p
  · have he : ((p - multiplierCount ys : ℕ) : ℝ) =
      (p : ℝ) - (multiplierCount ys : ℝ) := by
      rw [Nat.cast_sub hc]
    rw [← he]
    exact hdegree.hasOrder
  · rw [hzero (by omega)]
    exact hasOrder_zero _

/-- A real Schwartz multiplier belongs to its order-zero commutator class. -/
theorem realMultiplierOperator_operatorClass (g : SchwartzMap (Carrier N) ℝ) :
    OperatorClass 0 (realMultiplierOperator g) := by
  refine ⟨realMultiplierOperator g, realMultiplierOperator_bilinearTranspose g, ?_⟩
  intro ys
  have hstate : iteratedCommutator ys (realMultiplierOperator g) = 0 ∨
      ∃ a : TestFunction N, multiplierCount ys = 0 ∧
        iteratedCommutator ys (realMultiplierOperator g) = multiplierOperator a := by
    induction ys with
    | nil => exact Or.inr ⟨complexifyRealSchwartz g, by simp [multiplierCount], rfl⟩
    | cons Y ys ih =>
        rcases ih with hzero | ⟨a, hc, ha⟩
        · left
          simp [iteratedCommutator, OperatorGenerator.toOperator, hzero, operatorComm]
        · cases Y with
          | vectorField X =>
              right
              refine ⟨vectorFieldOperator X a, ?_, ?_⟩
              · simpa [multiplierCount, OperatorGenerator.isMultiplier] using hc
              · change operatorComm (vectorFieldOperator X)
                  (iteratedCommutator ys (realMultiplierOperator g)) = _
                rw [ha]
                rw [vectorFieldOperator_comm_multiplier]
          | multiplier b =>
              left
              change operatorComm (realMultiplierOperator b)
                (iteratedCommutator ys (realMultiplierOperator g)) = 0
              rw [ha]
              change operatorComm (multiplierOperator (complexifyRealSchwartz b))
                (multiplierOperator a) = 0
              rw [operatorComm_multiplier_multiplier]
  rcases hstate with hz | ⟨a, hc, ha⟩
  · rw [hz]
    exact hasOrder_zero _
  · rw [ha]
    simpa [hc] using (hasOrder_multiplierOperator_zero a)

/-- Every differential operator of degree `p` belongs to its commutator-order class,
provided it has a bilinear transpose. -/
theorem IsDiffOp.operatorClass {p : ℕ} {T Tt : Operator N}
    (hT : IsDiffOp p T) (htranspose : HasBilinearTranspose T Tt) :
    OperatorClass p T := by
  refine ⟨Tt, htranspose, ?_⟩
  intro ys
  simpa using iterated_diffOp_hasOrder hT ys

/-- The generator and closure facts for the commutator order class. -/
theorem b10Facts (N : ℕ) : Hormander.C.B10Facts N := by
  refine {
    lambda_mem := ?_
    multiplier_mem := fun g => realMultiplierOperator_operatorClass g
    vectorField_mem := ?_
    zero_mem := fun m => operatorClass_zero m
    add_mem := fun m A B hA hB => hA.add hB
    smul_mem := fun m c A hA => hA.smul c
    mono_mem := fun m m' A hA hm => hA.mono hm
    comp_mem := fun a b T U hT hU => hT.comp hU
    comm_vectorField := fun m T X hT => hT.comm_vectorField X
    comm_multiplier := fun m T g hT => hT.comm_realMultiplier g
    transpose_mem := fun m T Tt hT htranspose => hT.transpose_mem htranspose
  }
  · intro σ
    refine ⟨lambdaOperator σ, lambdaOperator_bilinearTranspose σ, ?_⟩
    intro ys
    exact iteratedCommutator_lambda_order σ ys
  · intro X
    simpa using
      (isDiffOp_vectorFieldOperator X).operatorClass (vectorField_bilinearTranspose X)

/-- The localized Bessel product is in `𝓞^σ`. -/
theorem localizedBesselOperator_operatorClass
    (η₁ η' : SchwartzMap (Carrier N) ℝ) (σ : ℝ) :
    OperatorClass σ
      ((realMultiplierOperator η').comp
        ((lambdaOperator σ).comp (realMultiplierOperator η₁))) := by
  have F : Hormander.C.B10Facts N := b10Facts N
  have hinner : OperatorClass (σ + 0)
      ((lambdaOperator σ).comp (realMultiplierOperator η₁)) :=
    (F.lambda_mem σ).comp (F.multiplier_mem η₁)
  have houter : OperatorClass (0 + (σ + 0))
      ((realMultiplierOperator η').comp
        ((lambdaOperator σ).comp (realMultiplierOperator η₁))) :=
    (F.multiplier_mem η').comp hinner
  simpa using houter

/-- The three vector-field commutators of the localized Bessel product satisfy these order bounds. -/
theorem localizedBesselOperator_depth_three
    (η₁ η' : SchwartzMap (Carrier N) ℝ) (σ : ℝ)
    (X Y : RealSchwartzVectorField N) :
    HasOrder σ (operatorComm (vectorFieldOperator Y)
        ((realMultiplierOperator η').comp
          ((lambdaOperator σ).comp (realMultiplierOperator η₁)))) ∧
    HasOrder σ (operatorComm (vectorFieldOperator X)
        (operatorComm (vectorFieldOperator Y)
          ((realMultiplierOperator η').comp
            ((lambdaOperator σ).comp (realMultiplierOperator η₁)))) ) ∧
    HasOrder σ (operatorComm
        (operatorComm (vectorFieldOperator X)
          (operatorComm (vectorFieldOperator Y)
            ((realMultiplierOperator η').comp
              ((lambdaOperator σ).comp (realMultiplierOperator η₁)))) )
        (vectorFieldOperator X)) := by
  exact (localizedBesselOperator_operatorClass η₁ η' σ).vectorField_depth_three X Y

end Hormander.B
