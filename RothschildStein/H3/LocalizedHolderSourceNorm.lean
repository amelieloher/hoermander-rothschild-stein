-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H3.HolderJetFirstNorm
public import RothschildStein.H3.LocalizedJetSourceNorm

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
open Set MeasureTheory TopologicalSpace
open scoped ENNReal BigOperators
namespace RothschildStein.H3

/-- The actual cutoff source is bounded solely by the local
source supremum, input supremum, full first-order fixed norm and
cutoff coefficient bounds. All weak data are the same selected jets. -/
theorem localized_holder_source_norm_le {N q : ℕ}
    (Ω U : Opens (Fin N → ℝ)) (G : S.DistanceGeometry Ω)
    (hU : (U : Set (Fin N → ℝ)) ⊆ Ω)
    (X : Fin (q + 1) → (Fin N → ℝ) → (Fin N → ℝ))
    (hX : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (X i) (U : Set (Fin N → ℝ)))
    {α : ℝ} (hα : 0 < α) (u : (Fin N → ℝ) → ℝ)
    (jet : List (Fin (q + 1)) → (Fin N → ℝ) → ℝ)
    (hzero : jet [] = u)
    (hj : ∀ I, wordWeight driftWeight I ≤ 2 → hasWeakWordDeriv X U I u (jet I) ∧
      holderENorm G.d α (U : Set (Fin N → ℝ)) (jet I) < ⊤)
    (φ : TestFunction U ℝ (⊤ : ℕ∞)) (A B : ℝ≥0∞)
    (hφ : eLpNorm φ ⊤ (volume.restrict (U : Set (Fin N → ℝ))) ≤ 1)
    (hA : ∀ i : Fin q, eLpNorm (fieldDerivative (X i.succ) φ) ⊤
      (volume.restrict (U : Set (Fin N → ℝ))) ≤ A)
    (hB : eLpNorm (sumSquaresWithDrift X φ) ⊤
      (volume.restrict (U : Set (Fin N → ℝ))) ≤ B) :
    eLpNorm (fun x => S.leibnizWordValue X [0] jet φ x +
      ∑ i : Fin q, S.leibnizWordValue X [i.succ, i.succ] jet φ x) ⊤ volume ≤
      eLpNorm (fun x => jet [0] x + ∑ i : Fin q, jet [i.succ, i.succ] x) ⊤
        (volume.restrict (U : Set (Fin N → ℝ))) +
      B * eLpNorm u ⊤ (volume.restrict (U : Set (Fin N → ℝ))) +
      2 * A * holderXENorm driftWeight X G.d U 1 α u := by
  let D := holderJetDriftData Ω U G hU X hα u jet hj
  have hb := localized_jet_source_norm_le X U ⊤ (by simp) u D jet hzero
    (fun _ => rfl) (fun _ => rfl) φ A B hφ hA hB
  exact hb.trans (add_le_add le_rfl
    (mul_le_mul' le_rfl (first_weakJetNorm_sum_le_holderX Ω U G hU X hX hα u jet hzero hj)))

end RothschildStein.H3
