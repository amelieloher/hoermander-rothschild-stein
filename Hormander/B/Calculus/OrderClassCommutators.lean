-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import Hormander.B.Calculus.OrderClassAlgebra
public import Hormander.B.Calculus.TransposeDuality

@[expose] public section

noncomputable section

namespace Hormander.B

variable {N : ℕ}

/-- Commuting a real Schwartz vector field past an `O^m` operator preserves its class. -/
theorem OperatorClass.comm_vectorField {m : ℝ} {T : Operator N}
    (hT : OperatorClass m T) (X : RealSchwartzVectorField N) :
    OperatorClass m (operatorComm (vectorFieldOperator X) T) := by
  rcases hT with ⟨Tt, hTt, horders⟩
  refine ⟨operatorComm Tt (-(vectorFieldOperator X) -
    realMultiplierOperator (vectorFieldDivergence X)),
    bilinearTranspose_commutator (vectorField_bilinearTranspose X) hTt, ?_⟩
  intro ys
  have h := horders (ys ++ [.vectorField X])
  rw [← iteratedCommutator_append_single ys (.vectorField X) T] at h
  have hc : multiplierCount (ys ++ [.vectorField X]) = multiplierCount ys := by
    simp [multiplierCount, OperatorGenerator.isMultiplier, List.filter_append]
  have h' := h
  rw [hc] at h'
  simpa [OperatorGenerator.toOperator] using h'

/-- Commuting a real Schwartz multiplier past an `O^m` operator lowers its class by one. -/
theorem OperatorClass.comm_realMultiplier {m : ℝ} {T : Operator N}
    (hT : OperatorClass m T) (g : SchwartzMap (Carrier N) ℝ) :
    OperatorClass (m - 1) (operatorComm (realMultiplierOperator g) T) := by
  rcases hT with ⟨Tt, hTt, horders⟩
  refine ⟨operatorComm Tt (realMultiplierOperator g),
    bilinearTranspose_commutator (realMultiplierOperator_bilinearTranspose g) hTt, ?_⟩
  intro ys
  have h := horders (ys ++ [.multiplier g])
  rw [← iteratedCommutator_append_single ys (.multiplier g) T] at h
  have hc : multiplierCount (ys ++ [.multiplier g]) = multiplierCount ys + 1 := by
    simp [multiplierCount, OperatorGenerator.isMultiplier, List.filter_append, List.filter]
  rw [hc] at h
  convert h using 1
  · rw [Nat.cast_add]
    ring
  · simp [OperatorGenerator.toOperator]

end Hormander.B
