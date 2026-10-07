-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import Hormander.B.Extension.Continuity

@[expose] public section

noncomputable section

namespace Hormander.B

variable {N : ℕ}

/-- An order estimate transfers to the bilinear transpose with the same constant. -/
theorem HasOrder.transpose {N : ℕ} {m : ℝ} {T Tt : Operator N}
    (hT : HasOrder m T) (htranspose : HasBilinearTranspose T Tt) :
    HasOrder m Tt := by
  intro s
  obtain ⟨C, hC⟩ := hT (-s - m)
  refine ⟨C, fun u => ?_⟩
  have h := transpose_bound_of_bound htranspose hC u
  have hleft : -((-s - m) + m) = s := by ring
  have hright : -(-s - m) = s + m := by ring
  simpa [hleft, hright] using h

/-- The real Bessel multiplier is bilinearly self-transpose. -/
theorem lambdaOperator_bilinearTranspose (s : ℝ) :
    HasBilinearTranspose (lambdaOperator (N := N) s) (lambdaOperator s) :=
  lambdaOperator_transpose s

/-- A real Schwartz multiplier is bilinearly self-transpose. -/
theorem realMultiplierOperator_bilinearTranspose
    (g : SchwartzMap (Carrier N) ℝ) :
    HasBilinearTranspose (realMultiplierOperator g) (realMultiplierOperator g) := by
  exact multiplierOperator_transpose (complexifyRealSchwartz g)

/-- Bilinear transposition preserves subtraction. -/
theorem HasBilinearTranspose.sub_local {A At B Bt : Operator N}
    (hA : HasBilinearTranspose A At) (hB : HasBilinearTranspose B Bt) :
    HasBilinearTranspose (A - B) (At - Bt) := by
  have hneg : HasBilinearTranspose (-B) (-Bt) := by
    simpa using hB.smul (-1 : ℂ)
  simpa only [sub_eq_add_neg] using hA.add hneg

/-- Bilinear transposition reverses commutators. -/
theorem bilinearTranspose_commutator {A At B Bt : Operator N}
    (hA : HasBilinearTranspose A At) (hB : HasBilinearTranspose B Bt) :
    HasBilinearTranspose (operatorComm A B) (operatorComm Bt At) := by
  have hAB := bilinearTranspose_comp hA hB
  have hBA := bilinearTranspose_comp hB hA
  simpa only [operatorComm] using hAB.sub_local hBA

/-- Integration by parts gives `Xᵗ = -X - div X`. -/
theorem vectorField_bilinearTranspose (V : RealSchwartzVectorField N) :
    HasBilinearTranspose (vectorFieldOperator V)
      (-(vectorFieldOperator V) - realMultiplierOperator (vectorFieldDivergence V)) :=
  vectorFieldOperator_transpose V

end Hormander.B
