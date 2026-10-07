-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H3.IntrinsicWordConvolution
public import RothschildStein.G2.MollifierUniform

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
open Set Filter
open scoped Topology
namespace RothschildStein.H3
variable {N q : ℕ} (G : HomogeneousGroup N)

/-- Group mollification commutes with an intrinsic word for continuous
compact suffix jets (BB Proposition 8.49, p. 379 and Theorem 8.52,
pp. 381–382). -/
theorem wordDerivative_groupRegularize_of_compact_intrinsic
    (X : Fin q → (Fin N → ℝ) → (Fin N → ℝ))
    (hX : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (X i))
    (hleft : ∀ i, G2.IsLeftInvariantField G (X i))
    {ν : G2.HomogeneousNorm G} (φ : G2.GroupMollifier G ν)
    (I : List (Fin q)) (f : (Fin N → ℝ) → ℝ)
    (jet : List (Fin q) → (Fin N → ℝ) → ℝ) (hzero : jet [] = f)
    (hi : ∀ J, J.IsSuffix I → hasIntrinsicWordDeriv X ⊤ J f (jet J))
    (hc : ∀ J, J.IsSuffix I → Continuous (jet J))
    (hs : ∀ J, J.IsSuffix I → HasCompactSupport (jet J))
    {ε : ℝ} (hε : 0 < ε) :
    wordDerivative X I (G2.groupRegularize G φ f ε) =
      G2.groupRegularize G φ (jet I) ε := by
  exact wordDerivative_convolution_of_compact_intrinsic G X hX hleft
    (G2.contDiff_groupMollifierScale G φ ε)
    (G2.hasCompactSupport_groupMollifierScale G φ hε) I f jet hzero hi hc hs

/-- Every actual word derivative of a group mollification converges
uniformly to its declared compact intrinsic jet, on the whole group.
BB Proposition 8.49, p. 379; no convergence of derivatives is assumed. -/
theorem tendstoUniformly_wordDerivative_groupRegularize
    (X : Fin q → (Fin N → ℝ) → (Fin N → ℝ))
    (hX : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (X i))
    (hleft : ∀ i, G2.IsLeftInvariantField G (X i))
    {ν : G2.HomogeneousNorm G} (φ : G2.GroupMollifier G ν)
    (I : List (Fin q)) (f : (Fin N → ℝ) → ℝ)
    (jet : List (Fin q) → (Fin N → ℝ) → ℝ) (hzero : jet [] = f)
    (hi : ∀ J, J.IsSuffix I → hasIntrinsicWordDeriv X ⊤ J f (jet J))
    (hc : ∀ J, J.IsSuffix I → Continuous (jet J))
    (hs : ∀ J, J.IsSuffix I → HasCompactSupport (jet J)) :
    TendstoUniformly (fun ε : ℝ => wordDerivative X I (G2.groupRegularize G φ f ε))
      (jet I) (𝓝[>] 0) := by
  have hreg := G2.tendstoUniformly_groupRegularize G φ
    (hc I (List.suffix_refl I)) (hs I (List.suffix_refl I))
  apply Metric.tendstoUniformly_iff.mpr
  intro δ hδ
  filter_upwards [Metric.tendstoUniformly_iff.mp hreg δ hδ, self_mem_nhdsWithin] with ε he hp x
  rw [wordDerivative_groupRegularize_of_compact_intrinsic G X hX hleft φ I f jet hzero hi hc hs hp]
  exact he x

end RothschildStein.H3
