-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H3.FrozenHolderMetricNorm
public import RothschildStein.H3.CompactGaugeHolderInput
public import RothschildStein.H2.HolderFiniteSum
public import RothschildStein.S.HolderZeroOrder
public import RothschildStein.S.IntrinsicUniqueness

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public section
noncomputable section
open Set TopologicalSpace
open scoped BigOperators ENNReal NNReal
namespace RothschildStein.H3

/-- Finite global jet norms put the drift-plus-square source
in the literal fixed zero-order Holder class. -/
theorem source_memHolderX_of_finite_jet_norms {N q : ℕ}
    (G : HomogeneousGroup N) (X : Fin (q + 1) → (Fin N → ℝ) → (Fin N → ℝ))
    (C : G2.ControlNormConclusion G driftWeight X) (a : ℝ≥0)
    (jet : List (Fin (q + 1)) → (Fin N → ℝ) → ℝ)
    (hj : ∀ I, wordWeight driftWeight I ≤ 2 →
      holderENorm (controlDistance univ driftWeight X) a univ (jet I) < ⊤) :
    memHolderX driftWeight X (controlDistance univ driftWeight X) ⊤ 0 a
      (fun x => jet [0] x + ∑ i : Fin q, jet [i.succ, i.succ] x) := by
  classical
  let metric : MetricSpace (ControlCarrier N) := gaugeMetric G C.norm C.constant_one C.symmetric
  have hb (I : List (Fin (q + 1))) (hI : wordWeight driftWeight I ≤ 2) :
      @H2.BoundedHolder (ControlCarrier N) metric a univ (jet I) := by
    have ht := hj I hI
    rw [frozen_holderENorm_eq_control_norm G driftWeight X C a univ] at ht
    exact ht
  have hw0 : wordWeight (driftWeight (q := q)) [0] ≤ 2 := by simp [wordWeight, driftWeight]
  have hw2 (i : Fin q) : wordWeight (driftWeight (q := q)) [i.succ, i.succ] ≤ 2 := by
    simp [wordWeight, driftWeight]
  have hs := @H2.boundedHolder_sum (ControlCarrier N) metric (Fin q) Finset.univ a univ
    (fun i => jet [i.succ, i.succ]) (fun i _ => hb _ (hw2 i))
  have ht := @H2.BoundedHolder.add (ControlCarrier N) metric a univ
    (jet [0]) (fun x => ∑ i : Fin q, jet [i.succ, i.succ] x) (hb [0] hw0) hs
  apply (S.memHolderX_zero_iff driftWeight X _ ⊤ a _).mpr
  change holderENorm (controlDistance univ driftWeight X) a univ
    (fun x => jet [0] x + ∑ i : Fin q, jet [i.succ, i.succ] x) < ⊤
  rw [frozen_holderENorm_eq_control_norm G driftWeight X C a univ]
  exact ht

/-- Every actual global intrinsic representative family of the
fixed compact input has a source in the fixed zero-order Holder class.
Intrinsic uniqueness identifies it with the proved compact Holder jets. -/
theorem source_memHolderX_of_compact_input {N q : ℕ}
    (G : HomogeneousGroup N) (X : Fin (q + 1) → (Fin N → ℝ) → (Fin N → ℝ))
    (hX : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (X i))
    (C : G2.ControlNormConclusion G driftWeight X) (U : Opens (Fin N → ℝ))
    (a : ℝ≥0) (ha : 0 < (a : ℝ)) (f : (Fin N → ℝ) → ℝ)
    (hf : memHolderXCompact driftWeight X (controlDistance univ driftWeight X) U 2 a f)
    (jet : List (Fin (q + 1)) → (Fin N → ℝ) → ℝ)
    (hi : ∀ I, wordWeight driftWeight I ≤ 2 →
      hasIntrinsicWordDeriv X ⊤ I ((U : Set (Fin N → ℝ)).indicator f) (jet I)) :
    memHolderX driftWeight X (controlDistance univ driftWeight X) ⊤ 0 a
      (fun x => jet [0] x + ∑ i : Fin q, jet [i.succ, i.succ] x) := by
  obtain ⟨T, _, v, _, hv⟩ := exists_global_holder_intrinsic_jets_of_memHolderXCompact_of_controlNorm
    G U driftWeight X hX C 2 ha hf
  apply source_memHolderX_of_finite_jet_norms G X C a jet
  intro I hI
  have he : jet I = v I := funext fun x =>
    S.hasIntrinsicWordDeriv_unique ⊤ X I (hi I hI) (hv I hI).1 (mem_univ x)
  rw [he]
  obtain ⟨A, hA⟩ := (hv I hI).2.2.2.2
  exact holderENorm_finite_of_compact_gauge_holder G driftWeight X C ha.le
    (hv I hI).2.1 (hv I hI).2.2.1 hA

end RothschildStein.H3
