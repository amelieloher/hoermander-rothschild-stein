-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.G3.ModelPackage
public import RothschildStein.P1.LiftedChart

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public section
noncomputable section
open Set
open scoped BigOperators
namespace RothschildStein.L1

/-- The concrete model and its chosen common commutator basis,
independent of the later coordinate and radius choices (BB pp. 511–532). -/
structure ModelData (k s N : ℕ) (w : Fin k → ℕ+) where
  G : HomogeneousGroup N
  B : Fin N → List (Fin k)
  v : Fin k → (Fin N → ℝ)
  Y : Fin k → (Fin N → ℝ) → (Fin N → ℝ)
  basis_weight : ∀ j, B j ≠ [] ∧ wordWeight w (B j) ≤ s ∧ G.weight j = wordWeight w (B j)
  basis_independent : LinearIndependent ℝ
    (fun j => (truncatedBracket (B j) : WordCoefficients k s w))
  basis_span : Submodule.span ℝ (Set.range (fun j =>
    (truncatedBracket (B j) : WordCoefficients k s w))) = formalSpan k s w
  generator_coords : ∀ i, (∑ j, v i j • (truncatedBracket (B j) : WordCoefficients k s w)) =
    truncatedBracket [i]
  inv_eq_neg : ∀ u, (fun j => MvPolynomial.eval u (G.inversePolynomial j)) = -u
  model_field_eq : ∀ i u, Y i u = fderiv ℝ (G.mul u) 0 (v i)
  model_field_smooth : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (Y i)
  model_field_invariant : ∀ i u z, fderiv ℝ (G.mul u) z (Y i z) = Y i (G.mul u z)
  model_field_homogeneous : ∀ i t, 0 < t → ∀ u,
    Y i (G.dilate t u) = t ^ (-((w i : ℕ) : ℤ)) • G.dilate t (Y i u)
  model_free : ∀ u, FreeAt w s Y u ∧ StepSpansAt w s Y u
  model_nilpotent : ∀ I : List (Fin k), s < wordWeight w I → wordBracket Y I = 0
  model_basis_origin : ∀ j, wordBracket Y (B j) 0 = Pi.single j 1
  model_exponential : ∀ u, (∑ j, u j • wordBracket Y (B j) u) = u

end RothschildStein.L1
