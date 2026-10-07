-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module
public import RothschildStein.G3.ModelWords
public import RothschildStein.G3.ModelDilation
public import RothschildStein.G1.CommutatorSchedule
@[expose] public section
noncomputable section
namespace RothschildStein.G3

/-- Exact finite logarithm of the signed commutator recursion, in
pullback order (BB Lemma 9.26, pp. 417–419; corrected intermediate sign). -/
def quasiExponentialLog {a s : ℕ} {p : Fin a → ℕ+} :
    List (Fin a) → coefficientLieAlgebra a s p
  | [] => 0
  | [i] => wordLieElement [i]
  | i :: j :: I =>
      let A : coefficientLieAlgebra a s p := wordLieElement [i]
      let B := quasiExponentialLog (j :: I)
      modelProduct (modelProduct (modelProduct A B) (-A)) (-B)

/-- Weighted parameterization of the exact finite commutator logarithm
(BB Lemma 9.26, pp. 417–419). -/
def quasiExponentialLogAt {a s : ℕ} {p : Fin a → ℕ+}
    (t : ℝ) (I : List (Fin a)) : coefficientLieAlgebra a s p :=
  modelDilation t (quasiExponentialLog I)

/-- A one-letter logarithm carries precisely its assigned weighted
primitive time (BB (9.13), p. 417). -/
theorem quasiExponentialLogAt_singleton {a s : ℕ} {p : Fin a → ℕ+}
    (t : ℝ) (i : Fin a) :
    quasiExponentialLogAt (s := s) (p := p) t [i] =
      t ^ (p i : ℕ) • (wordLieElement [i] : coefficientLieAlgebra a s p) := by
  apply Subtype.ext
  change finiteDilate t (truncatedBracket [i]) = t ^ (p i : ℕ) • truncatedBracket [i]
  simpa only [wordWeight, List.map_singleton, List.sum_singleton] using
    finiteDilate_truncatedBracket (s := s) t [i]

/-- Exact primitive factor count, including the singleton case
(BB Lemma 9.26, p. 417). -/
theorem quasiExponential_primitive_count {a : ℕ} (I : List (Fin a)) (hI : I ≠ []) :
    (G1.commutatorSchedule I).length = 3 * 2 ^ (I.length - 1) - 2 := by
  have h := G1.commutatorSchedule_length I hI
  omega
end RothschildStein.G3
