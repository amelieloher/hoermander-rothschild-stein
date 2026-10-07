-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module
public import RothschildStein.G3.BCH
@[expose] public section
noncomputable section
namespace RothschildStein.G3

/-- Lowering the positive weighted cutoff retains exactly the smaller
word coefficients (BB pp. 468, 524–525). -/
def lowerCutoff {a s t : ℕ} {p : Fin a → ℕ+} (hst : s ≤ t)
    (f : FiniteWordAlgebra a t p) : FiniteWordAlgebra a s p :=
  fun J => f (boundedWord p J.val ((boundedWord_weight J).trans hst))

/-- Cutoff restriction agrees with zero extension on every retained word
(BB p. 468; BB p. 525). -/
theorem extend_lowerCutoff {a s t : ℕ} {p : Fin a → ℕ+} (hst : s ≤ t)
    (f : FiniteWordAlgebra a t p) (J : List (Fin a)) (hJ : wordWeight p J ≤ s) :
    extend (lowerCutoff hst f : WordCoefficients a s p) J = extend f J := by
  simp only [extend]
  split
  · split
    · rfl
    · rename_i h
      exact False.elim (h (hJ.trans hst))
  · rename_i h
    exact False.elim (h hJ)

/-- Multiplication is compatible with changing the weighted cutoff
(BB p. 468; BB Proposition 10.44, p. 525). -/
theorem lowerCutoff_mul {a s t : ℕ} {p : Fin a → ℕ+} (hst : s ≤ t)
    (f g : FiniteWordAlgebra a t p) : lowerCutoff hst (f * g) = lowerCutoff hst f * lowerCutoff hst g := by
  funext J
  change wordConvolution (extend f) (extend g) J.val =
    wordConvolution (extend (lowerCutoff hst f)) (extend (lowerCutoff hst g)) J.val
  exact (convolution_eq_of_eq_through (extend_lowerCutoff hst f) (extend_lowerCutoff hst g)
    J.val (boundedWord_weight J)).symm

/-- Algebra homomorphism between finite weighted quotients
(BB pp. 468, 524–525). -/
def cutoffHom {a s t : ℕ} {p : Fin a → ℕ+} (hst : s ≤ t) :
    FiniteWordAlgebra a t p →ₐ[ℝ] FiniteWordAlgebra a s p where
  toFun := lowerCutoff hst
  map_one' := by funext J; rfl
  map_mul' := lowerCutoff_mul hst
  map_zero' := rfl
  map_add' _ _ := rfl
  commutes' r := by
    rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one]
    funext J
    rfl

/-- Cutoff homomorphisms preserve every lower-order bound (BB p. 468). -/
theorem cutoffHom_order {a s t : ℕ} {p : Fin a → ℕ+} (hst : s ≤ t) {k : ℕ}
    {f : FiniteWordAlgebra a t p} (hf : FiniteOrderAtLeast k f) :
    FiniteOrderAtLeast k (cutoffHom hst f) := by
  apply (finiteOrderAtLeast_iff k _).mpr
  intro J hJ
  exact (finiteOrderAtLeast_iff k f).mp hf
    (boundedWord p J.val ((boundedWord_weight J).trans hst)) hJ

/-- Exponentiation is consistent as the finite cutoff increases (BB p. 468). -/
theorem cutoffHom_finiteExp {a s t : ℕ} {p : Fin a → ℕ+} (hst : s ≤ t)
    {f : FiniteWordAlgebra a t p} (hf : FiniteOrderAtLeast 1 f) :
    cutoffHom hst (finiteExp f) = finiteExp (cutoffHom hst f) :=
  map_finiteExp (cutoffHom hst) hf (cutoffHom_order hst hf)

/-- BCH is consistent as the finite cutoff increases (BB pp. 468–470). -/
theorem cutoffHom_finiteBCH {a s t : ℕ} {p : Fin a → ℕ+} (hst : s ≤ t)
    {f g : FiniteWordAlgebra a t p} (hf : FiniteOrderAtLeast 1 f)
    (hg : FiniteOrderAtLeast 1 g) :
    cutoffHom hst (finiteBCH f g) = finiteBCH (cutoffHom hst f) (cutoffHom hst g) :=
  map_finiteBCH (cutoffHom hst) (fun _ h => cutoffHom_order hst h) hf hg

end RothschildStein.G3
