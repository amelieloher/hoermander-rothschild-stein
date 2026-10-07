-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H3.HolderCutoffProduct
public import RothschildStein.H3.LocalizedJetSource
public import RothschildStein.H2.HolderFiniteSum

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public section
noncomputable section
open Set
open scoped ENNReal NNReal BigOperators
namespace RothschildStein.H3

/-- Every ordered cutoff-source term has its global full
Hölder product bound from the same local input jets. Both horizontal
cross terms are retained. Compactness belongs to the cutoff. -/
theorem localized_source_holder_norm_le_of_controlNorm {N q : ℕ} (G : HomogeneousGroup N)
    (X : Fin (q + 1) → (Fin N → ℝ) → (Fin N → ℝ))
    (Hc : G2.ControlNormConclusion G driftWeight X)
    {α : ℝ≥0} (u φ : (Fin N → ℝ) → ℝ)
    (jet : List (Fin (q + 1)) → (Fin N → ℝ) → ℝ) (hzero : jet [] = u)
    (hcφ : HasCompactSupport φ) :
    let metric : MetricSpace (ControlCarrier N) :=
      gaugeMetric G Hc.norm Hc.constant_one Hc.symmetric
    ∀ A : Set (ControlCarrier N), IsOpen A → tsupport φ ⊆ A →
    (∀ I, @H2.BoundedHolder (ControlCarrier N) metric α univ
      (fun x => wordDerivative X I φ x)) →
    @H2.BoundedHolder (ControlCarrier N) metric α A u →
    (∀ i : Fin q, @H2.BoundedHolder (ControlCarrier N) metric α A (jet [i.succ])) →
    @H2.BoundedHolder (ControlCarrier N) metric α A
      (fun x => jet [0] x + ∑ i : Fin q, jet [i.succ, i.succ] x) →
    let normG := fun f : (Fin N → ℝ) → ℝ =>
      @H2.boundedHolderNorm (ControlCarrier N) metric α univ (fun x => f x)
    let normA := fun f : (Fin N → ℝ) → ℝ =>
      @H2.boundedHolderNorm (ControlCarrier N) metric α A (fun x => f x)
    normG (fun x => S.leibnizWordValue X [0] jet φ x +
      ∑ i : Fin q, S.leibnizWordValue X [i.succ, i.succ] jet φ x) ≤
      normG φ * normA (fun x => jet [0] x + ∑ i : Fin q, jet [i.succ, i.succ] x) +
      2 * (∑ i : Fin q, normG (wordDerivative X [i.succ] φ) * normA (jet [i.succ])) +
      (normG (wordDerivative X [0] φ) +
        ∑ i : Fin q, normG (wordDerivative X [i.succ, i.succ] φ)) * normA u := by
  classical
  let metric : MetricSpace (ControlCarrier N) :=
    gaugeMetric G Hc.norm Hc.constant_one Hc.symmetric
  dsimp only
  intro A hA hsφ hφ hu hj hF
  let normG := fun f : (Fin N → ℝ) → ℝ =>
    @H2.boundedHolderNorm (ControlCarrier N) metric α univ (fun x => f x)
  let normA := fun f : (Fin N → ℝ) → ℝ =>
    @H2.boundedHolderNorm (ControlCarrier N) metric α A (fun x => f x)
  have hprod (I : List (Fin (q + 1))) (f : (Fin N → ℝ) → ℝ)
      (hf : @H2.BoundedHolder (ControlCarrier N) metric α A f) :
      normG (fun x => wordDerivative X I φ x * f x) ≤
        normG (wordDerivative X I φ) * normA f := by
    have hs := S.tsupport_wordDerivative_subset X I φ
    have hc : HasCompactSupport (wordDerivative X I φ) :=
      hcφ.of_isClosed_subset (isClosed_tsupport _) hs
    exact boundedHolderNorm_cutoff_product_of_controlNorm Hc hA hc
      (hs.trans hsφ) (hφ I) hf
  let F := fun x => jet [0] x + ∑ i : Fin q, jet [i.succ, i.succ] x
  have hb := hprod [] F hF
  have hi := H2.boundedHolderNorm_sum_le Finset.univ α univ
    (fun i : Fin q => fun x : ControlCarrier N => wordDerivative X [i.succ] φ x * jet [i.succ] x)
  have hi' : normG (fun x => ∑ i : Fin q, wordDerivative X [i.succ] φ x * jet [i.succ] x) ≤
      ∑ i : Fin q, normG (wordDerivative X [i.succ] φ) * normA (jet [i.succ]) :=
    hi.trans (Finset.sum_le_sum (fun i _ => hprod [i.succ] (jet [i.succ]) (hj i)))
  have hdiag := H2.boundedHolderNorm_sum_le Finset.univ α univ
    (fun i : Fin q => fun x : ControlCarrier N => wordDerivative X [i.succ, i.succ] φ x * u x)
  have hdiag' := hdiag.trans (Finset.sum_le_sum
    (fun i _ => hprod [i.succ, i.succ] u hu))
  have hL : normG (fun x => sumSquaresWithDrift X φ x * u x) ≤
      (normG (wordDerivative X [0] φ) +
        ∑ i : Fin q, normG (wordDerivative X [i.succ, i.succ] φ)) * normA u := by
    have he : (fun x => sumSquaresWithDrift X φ x * u x) =
        (fun x => wordDerivative X [0] φ x * u x +
          ∑ i : Fin q, wordDerivative X [i.succ, i.succ] φ x * u x) := by
      funext x
      simp only [sumSquaresWithDrift, wordDerivative, add_mul, Finset.sum_mul]
    rw [he]
    have hh := H2.boundedHolderNorm_add_le.trans (add_le_add (hprod [0] u hu) hdiag')
    apply hh.trans_eq
    rw [← Finset.sum_mul, ← add_mul]
  have hc : normG (fun x => 2 * ∑ i : Fin q, wordDerivative X [i.succ] φ x * jet [i.succ] x) ≤
      2 * (∑ i : Fin q, normG (wordDerivative X [i.succ] φ) * normA (jet [i.succ])) := by
    have he := H2.boundedHolderNorm_smul (δ := α) (U := (univ : Set (ControlCarrier N)))
      (2 : ℝ) (fun x => ∑ i : Fin q, wordDerivative X [i.succ] φ x * jet [i.succ] x)
    change normG (fun x => 2 * ∑ i : Fin q, wordDerivative X [i.succ] φ x * jet [i.succ] x) = _ at he
    norm_num at he
    rw [he]
    exact mul_le_mul' le_rfl hi'
  have he : (fun x => S.leibnizWordValue X [0] jet φ x +
      ∑ i : Fin q, S.leibnizWordValue X [i.succ, i.succ] jet φ x) =
      (fun x => φ x * F x +
        2 * (∑ i : Fin q, wordDerivative X [i.succ] φ x * jet [i.succ] x) +
        sumSquaresWithDrift X φ x * u x) := by
    funext x
    rw [localized_jet_source X u φ jet hzero x]
    simp only [F, wordDerivative, mul_comm]
  exact (congrArg normG he).le.trans (H2.boundedHolderNorm_add_le.trans
    (add_le_add (H2.boundedHolderNorm_add_le.trans (add_le_add hb hc)) hL))

end RothschildStein.H3
