-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import Hormander.D.SupportFactorization

@[expose] public section

namespace Hormander.D

/-- The square commutator expansion for linear actions on Schwartz functions. -/
theorem commutator_square_expansion {N : ℕ} (X A : Hormander.B.Operator N) :
    Hormander.B.operatorComm (X.comp X) A =
      (2 : ℂ) • X.comp (Hormander.B.operatorComm X A) +
        Hormander.B.operatorComm (Hormander.B.operatorComm X A) X := by
  ext u
  simp [Hormander.B.operatorComm, LinearMap.comp_apply]
  ring

theorem operatorComm_add_left {N : ℕ} (A B C : Hormander.B.Operator N) :
    Hormander.B.operatorComm (A + B) C =
      Hormander.B.operatorComm A C + Hormander.B.operatorComm B C := by
  ext u
  simp [Hormander.B.operatorComm]
  abel

theorem operatorComm_sum_left {N : ℕ} {ι : Type*} [Fintype ι]
    (A : ι → Hormander.B.Operator N) (B : Hormander.B.Operator N) :
    Hormander.B.operatorComm (∑ i, A i) B =
      ∑ i, Hormander.B.operatorComm (A i) B := by
  classical
  ext u
  simp [Hormander.B.operatorComm]

/-- Expanding the commutator of a sum of squares with the localized operator. -/
theorem commutator_sum_squares_expansion {N k : ℕ}
    (X : Fin k → Hormander.B.Operator N)
    (X₀ c A : Hormander.B.Operator N) :
    Hormander.B.operatorComm ((∑ j, (X j).comp (X j)) + X₀ + c) A =
      (∑ j : Fin k, ((2 : ℂ) • (X j).comp (Hormander.B.operatorComm (X j) A) +
        Hormander.B.operatorComm (Hormander.B.operatorComm (X j) A) (X j))) +
        Hormander.B.operatorComm X₀ A + Hormander.B.operatorComm c A := by
  rw [operatorComm_add_left, operatorComm_add_left, operatorComm_sum_left]
  congr 1
  congr 1
  apply Finset.sum_congr rfl
  intro j hj
  exact commutator_square_expansion (X j) A

end Hormander.D

end
