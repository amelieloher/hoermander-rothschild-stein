-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H3.IntrinsicWordMollification
public import RothschildStein.S.Sobolev
public import RothschildStein.Definitions.driftWeight
public import RothschildStein.Definitions.sumSquaresWithDrift
public import RothschildStein.G2.MollifierIntegrability

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
open Set MeasureTheory Filter
open scoped Topology
open scoped ENNReal BigOperators
namespace RothschildStein.H3
variable {N q : ℕ} (G : HomogeneousGroup N)

/-- The weighted order-two intrinsic jet family suffices for
actual word/mollifier commutation. Suffixes remain in that family.
BB Proposition 8.49, p. 379. -/
theorem wordDerivative_groupRegularize_of_weight_two_jets
    (X : Fin (q + 1) → (Fin N → ℝ) → (Fin N → ℝ))
    (hX : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (X i))
    (hleft : ∀ i, G2.IsLeftInvariantField G (X i))
    {ν : G2.HomogeneousNorm G} (φ : G2.GroupMollifier G ν)
    (f : (Fin N → ℝ) → ℝ) (jet : List (Fin (q + 1)) → (Fin N → ℝ) → ℝ)
    (hzero : jet [] = f)
    (hi : ∀ I, wordWeight driftWeight I ≤ 2 → hasIntrinsicWordDeriv X ⊤ I f (jet I))
    (hc : ∀ I, wordWeight driftWeight I ≤ 2 → Continuous (jet I))
    (hs : ∀ I, wordWeight driftWeight I ≤ 2 → HasCompactSupport (jet I))
    (I : List (Fin (q + 1))) (hI : wordWeight driftWeight I ≤ 2)
    {ε : ℝ} (hε : 0 < ε) :
    wordDerivative X I (G2.groupRegularize G φ f ε) = G2.groupRegularize G φ (jet I) ε := by
  have hw (J : List (Fin (q + 1))) (hJ : J.IsSuffix I) : wordWeight driftWeight J ≤ 2 :=
    (S.wordWeight_sublist_le driftWeight hJ.sublist).trans hI
  exact wordDerivative_groupRegularize_of_compact_intrinsic G X hX hleft φ I f jet hzero
    (fun J hJ => hi J (hw J hJ)) (fun J hJ => hc J (hw J hJ)) (fun J hJ => hs J (hw J hJ)) hε

/-- Actual weighted order-two mollifier jets converge uniformly
from precisely the finite-order intrinsic input family (BB p. 379). -/
theorem tendstoUniformly_groupRegularize_of_weight_two_jets
    (X : Fin (q + 1) → (Fin N → ℝ) → (Fin N → ℝ))
    (hX : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (X i))
    (hleft : ∀ i, G2.IsLeftInvariantField G (X i))
    {ν : G2.HomogeneousNorm G} (φ : G2.GroupMollifier G ν)
    (f : (Fin N → ℝ) → ℝ) (jet : List (Fin (q + 1)) → (Fin N → ℝ) → ℝ)
    (hzero : jet [] = f)
    (hi : ∀ I, wordWeight driftWeight I ≤ 2 → hasIntrinsicWordDeriv X ⊤ I f (jet I))
    (hc : ∀ I, wordWeight driftWeight I ≤ 2 → Continuous (jet I))
    (hs : ∀ I, wordWeight driftWeight I ≤ 2 → HasCompactSupport (jet I))
    (I : List (Fin (q + 1))) (hI : wordWeight driftWeight I ≤ 2) :
    TendstoUniformly (fun ε : ℝ => wordDerivative X I (G2.groupRegularize G φ f ε))
      (jet I) (𝓝[>] 0) := by
  have hw (J : List (Fin (q + 1))) (hJ : J.IsSuffix I) : wordWeight driftWeight J ≤ 2 :=
    (S.wordWeight_sublist_le driftWeight hJ.sublist).trans hI
  exact tendstoUniformly_wordDerivative_groupRegularize G X hX hleft φ I f jet hzero
    (fun J hJ => hi J (hw J hJ)) (fun J hJ => hc J (hw J hJ)) (fun J hJ => hs J (hw J hJ))

/-- The actual sum-of-squares operator on the mollified input
is mollification of the drift plus diagonal second intrinsic jets.
BB Proposition 8.49, p. 379; finite-sum interchange uses absolute convergence. -/
theorem sumSquaresWithDrift_groupRegularize_of_intrinsic_jets
    (X : Fin (q + 1) → (Fin N → ℝ) → (Fin N → ℝ))
    (hX : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (X i))
    (hleft : ∀ i, G2.IsLeftInvariantField G (X i))
    {ν : G2.HomogeneousNorm G} (φ : G2.GroupMollifier G ν)
    (f : (Fin N → ℝ) → ℝ) (jet : List (Fin (q + 1)) → (Fin N → ℝ) → ℝ)
    (hzero : jet [] = f)
    (hi : ∀ I, wordWeight driftWeight I ≤ 2 → hasIntrinsicWordDeriv X ⊤ I f (jet I))
    (hc : ∀ I, wordWeight driftWeight I ≤ 2 → Continuous (jet I))
    (hs : ∀ I, wordWeight driftWeight I ≤ 2 → HasCompactSupport (jet I))
    {ε : ℝ} (hε : 0 < ε) :
    sumSquaresWithDrift X (G2.groupRegularize G φ f ε) =
      G2.groupRegularize G φ (fun x => jet [0] x + ∑ i : Fin q, jet [i.succ, i.succ] x) ε := by
  classical
  have hw0 : wordWeight (driftWeight (q := q)) [0] ≤ 2 := by simp [wordWeight, driftWeight]
  have hw2 (i : Fin q) : wordWeight (driftWeight (q := q)) [i.succ, i.succ] ≤ 2 := by
    simp [wordWeight, driftWeight]
  have hd := wordDerivative_groupRegularize_of_weight_two_jets G X hX hleft φ f jet hzero hi hc hs [0] hw0 hε
  have hdd (i : Fin q) := wordDerivative_groupRegularize_of_weight_two_jets G X hX hleft φ f jet hzero hi hc hs
    [i.succ, i.succ] (hw2 i) hε
  funext x
  change wordDerivative X [0] (G2.groupRegularize G φ f ε) x +
    ∑ i : Fin q, wordDerivative X [i.succ, i.succ] (G2.groupRegularize G φ f ε) x = _
  simp only [hd, hdd]
  have hint (I : List (Fin (q + 1))) (hI : wordWeight driftWeight I ≤ 2) :
      Integrable (fun y => G2.groupMollifierScale G φ ε y * jet I (G.mul (G.inv y) x)) volume :=
    G2.groupRegularize_existsAt G φ hε (p := (1 : ℝ≥0∞)) le_rfl
      ((hc I hI).memLp_of_hasCompactSupport (hs I hI)) x
  simp only [G2.groupRegularize, G2.groupConvolution_eq_integral, mul_add, Finset.mul_sum]
  rw [integral_add (hint [0] hw0) (integrable_finsetSum _ (fun i _ => hint [i.succ, i.succ] (hw2 i))),
    integral_finsetSum _ (fun i _ => hint [i.succ, i.succ] (hw2 i))]

end RothschildStein.H3
