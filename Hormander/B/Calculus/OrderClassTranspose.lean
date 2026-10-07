-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import Hormander.B.Calculus.OrderClassCommutators

@[expose] public section

noncomputable section

namespace Hormander.B

variable {N : ℕ}

/-- The generator appearing when a commutator word is transposed. -/
def generatorBilinearTranspose : OperatorGenerator N → Operator N
  | .vectorField X => -(vectorFieldOperator X) -
      realMultiplierOperator (vectorFieldDivergence X)
  | .multiplier g => realMultiplierOperator g

/-- Apply the bilinear transposes of the generators in a commutator word. -/
def transposeGeneratorWord : List (OperatorGenerator N) → Operator N → Operator N
  | [], T => T
  | Y :: ys, T => operatorComm (generatorBilinearTranspose Y) (transposeGeneratorWord ys T)

private theorem operatorComm_smul_left_local (A B : Operator N) (c : ℂ) :
    operatorComm (c • A) B = c • operatorComm A B := by
  ext u x
  simp [operatorComm, LinearMap.smul_comp, LinearMap.comp_smul]
  ring

private theorem bilinearTranspose_symm_local {A B : Operator N}
    (h : HasBilinearTranspose A B) : HasBilinearTranspose B A := by
  intro u v
  calc
    bilinearPairing (B u) v = bilinearPairing v (B u) := bilinearPairing_comm _ _
    _ = bilinearPairing (A v) u := (h v u).symm
    _ = bilinearPairing u (A v) := (bilinearPairing_comm _ _).symm

private theorem generatorBilinearTranspose_transpose (Y : OperatorGenerator N) :
    HasBilinearTranspose (generatorBilinearTranspose Y) Y.toOperator := by
  cases Y with
  | vectorField X => exact bilinearTranspose_symm_local (vectorField_bilinearTranspose X)
  | multiplier g => exact realMultiplierOperator_bilinearTranspose g

/-- The transpose of a word of commutators is the reverse-action word, up to its sign. -/
theorem transposeWord_bilinearTranspose (ys : List (OperatorGenerator N))
    (T Tt : Operator N) (hT : HasBilinearTranspose T Tt) :
    HasBilinearTranspose (transposeGeneratorWord ys T)
      (((-1 : ℂ) ^ ys.length) • iteratedCommutator ys Tt) := by
  induction ys generalizing T Tt with
  | nil => simpa [transposeGeneratorWord, iteratedCommutator]
  | cons Y ys ih =>
      have htail := ih T Tt hT
      have hcomm := bilinearTranspose_commutator
        (generatorBilinearTranspose_transpose Y) htail
      have hop : operatorComm
          (((( -1 : ℂ) ^ ys.length) • iteratedCommutator ys Tt)) Y.toOperator =
          (((-1 : ℂ) ^ (ys.length + 1)) •
            operatorComm Y.toOperator (iteratedCommutator ys Tt)) := by
        rw [operatorComm_smul_left_local, operatorComm_antisymm_local]
        simp [pow_succ, mul_comm]
      rw [show transposeGeneratorWord (Y :: ys) T =
        operatorComm (generatorBilinearTranspose Y) (transposeGeneratorWord ys T) by rfl,
        show iteratedCommutator (Y :: ys) Tt =
          operatorComm Y.toOperator (iteratedCommutator ys Tt) by rfl]
      simpa [hop, List.length_cons] using hcomm

/-- A commutator word in the transposed generators preserves the class order. -/
theorem OperatorClass.transpose_word_class {m : ℝ} {T : Operator N}
    (hT : OperatorClass m T) (ys : List (OperatorGenerator N)) :
    OperatorClass (m - (multiplierCount ys : ℝ)) (transposeGeneratorWord ys T) := by
  induction ys with
  | nil => simpa [multiplierCount, transposeGeneratorWord] using hT
  | cons Y ys ih =>
    cases Y with
    | vectorField X =>
        let k : ℝ := m - (multiplierCount ys : ℝ)
        have hX : OperatorClass k
            (operatorComm (vectorFieldOperator X) (transposeGeneratorWord ys T)) := by
          simpa [k] using ih.comm_vectorField X
        have hdiv₀ := ih.comm_realMultiplier (vectorFieldDivergence X)
        have hdiv : OperatorClass k
            (operatorComm (realMultiplierOperator (vectorFieldDivergence X))
              (transposeGeneratorWord ys T)) := by
          exact hdiv₀.mono (by dsimp [k]; exact sub_le_self _ (by norm_num))
        have he : operatorComm (generatorBilinearTranspose (.vectorField X))
            (transposeGeneratorWord ys T) =
            (-1 : ℂ) • operatorComm (vectorFieldOperator X) (transposeGeneratorWord ys T) +
              (-1 : ℂ) • operatorComm
                (realMultiplierOperator (vectorFieldDivergence X)) (transposeGeneratorWord ys T) := by
          ext u x
          simp [generatorBilinearTranspose, operatorComm, LinearMap.neg_comp,
            LinearMap.sub_comp, LinearMap.comp_neg, LinearMap.comp_sub]
          ring
        change OperatorClass (m - (multiplierCount (.vectorField X :: ys) : ℝ))
          (operatorComm (generatorBilinearTranspose (.vectorField X))
            (transposeGeneratorWord ys T))
        rw [he]
        have hout := (hX.smul (-1 : ℂ)).add (hdiv.smul (-1 : ℂ))
        have hc : multiplierCount (.vectorField X :: ys) = multiplierCount ys := by
          simp [multiplierCount, OperatorGenerator.isMultiplier]
        rw [hc]
        simpa [k] using hout
    | multiplier g =>
        change OperatorClass (m - (multiplierCount (.multiplier g :: ys) : ℝ))
          (operatorComm (realMultiplierOperator g) (transposeGeneratorWord ys T))
        have h := ih.comm_realMultiplier g
        convert h using 1
        · simp [multiplierCount, List.filter, OperatorGenerator.isMultiplier]
          ring

/-- Transposition preserves every commutator-order class. -/
theorem OperatorClass.transpose_mem {m : ℝ} {T Tt : Operator N}
    (hT : OperatorClass m T) (htranspose : HasBilinearTranspose T Tt) :
    OperatorClass m Tt := by
  refine ⟨T, bilinearTranspose_symm_local htranspose, ?_⟩
  intro ys
  rcases OperatorClass.transpose_word_class hT ys with ⟨_, _, horders⟩
  have hword : HasOrder (m - (multiplierCount ys : ℝ)) (transposeGeneratorWord ys T) := by
    simpa [multiplierCount, iteratedCommutator] using horders []
  have htrans := transposeWord_bilinearTranspose ys T Tt htranspose
  have hscaled := hword.transpose htrans
  have hc : ((-1 : ℂ) ^ ys.length) * ((-1 : ℂ) ^ ys.length) = 1 := by
    rw [← mul_pow, neg_mul_neg]
    simp
  have hcancel : HasOrder (m - (multiplierCount ys : ℝ))
      (iteratedCommutator ys Tt) := by
    have := hscaled.smul ((-1 : ℂ) ^ ys.length)
    simpa [smul_smul, hc] using this
  exact hcancel

end Hormander.B
