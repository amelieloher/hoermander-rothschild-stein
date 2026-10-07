-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H3.LocalizedSourceFirstNorm
public import RothschildStein.H3.QuasiballSourceHolderCoefficients
public import RothschildStein.H3.QuasiballDomain

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public section
noncomputable section
open Set MeasureTheory TopologicalSpace
open scoped ENNReal NNReal BigOperators
namespace RothschildStein.H3

/-- The exact cutoff source has the alpha and two-plus-alpha
losses with the complete local first-order norm. Constants are chosen
before the center, radii, original solution and normalized weak jets. -/
theorem quasiball_source_holder_loss_of_controlNorm {N q : ℕ}
    (G : HomogeneousGroup N) (H : H1.StandingHypotheses G q)
    (C : G2.ControlNormConclusion G driftWeight H.fields)
    (ν : G2.HomogeneousNorm G) (hν : ν.Smooth)
    {a : ℝ≥0} (ha : 0 < a) (ha1 : (a : ℝ) ≤ 1)
    {Rmax : ℝ} (hRmax : 0 < Rmax) :
    ∃ A B : ℝ, 0 < A ∧ 0 < B ∧ ∀ z : Fin N → ℝ, ∀ t s : ℝ,
      0 < t → t < s → s / 2 ≤ t → s - t ≤ Rmax →
      let U := quasiballDomain G ν z s
      ∀ u f : (Fin N → ℝ) → ℝ,
      ∀ jet : List (Fin (q + 1)) → (Fin N → ℝ) → ℝ,
      jet [] = u →
      (∀ I, wordWeight driftWeight I ≤ 2 → hasWeakWordDeriv H.fields U I u (jet I) ∧
        holderENorm (controlDistance univ driftWeight H.fields) a (U : Set (Fin N → ℝ)) (jet I) < ⊤) →
      holderENorm (controlDistance univ driftWeight H.fields) a (U : Set (Fin N → ℝ)) f < ⊤ →
      hasDistributionEquationWithDrift U H.fields (fun i => (H.fields_smooth G i).contDiffOn)
        (Distribution.ofFun U u volume (⊤ : ℕ∞)) f →
      holderENorm (controlDistance univ driftWeight H.fields) a univ
        (fun x => S.leibnizWordValue H.fields [0] jet (smoothQuasiballCutoff G ν z t s) x +
          ∑ i : Fin q, S.leibnizWordValue H.fields [i.succ, i.succ] jet
            (smoothQuasiballCutoff G ν z t s) x) ≤
        ENNReal.ofReal (A * (s - t) ^ (-(a : ℝ))) *
          holderENorm (controlDistance univ driftWeight H.fields) a (U : Set (Fin N → ℝ)) f +
        ENNReal.ofReal (B * (s - t) ^ (-(2 + (a : ℝ)))) *
          holderXENorm driftWeight H.fields (controlDistance univ driftWeight H.fields) U 1 a u := by
  let metric := gaugeMetric G C.norm C.constant_one C.symmetric
  obtain ⟨A, B, hA, hB, hcoeff⟩ := exists_quasiball_source_holder_coefficients G H C ν hν ha1 hRmax
  obtain ⟨c, _hc, hword⟩ := exists_quasiball_cutoff_word_holder_power_constants G H C ν hν ha1 hRmax
  refine ⟨A, B, hA, hB, ?_⟩
  intro z t s ht hts hhalf hgap U u f jet hz hj hf heq
  let φ : TestFunction U ℝ (⊤ : ℕ∞) :=
    ⟨smoothQuasiballCutoff G ν z t s,
      smoothQuasiballCutoff_contDiff G ν hν z ht hts,
      smoothQuasiballCutoff_compact G ν z hts,
      (smoothQuasiballCutoff_tsupport G ν z hts).trans (intermediate_quasiball_subset G ν z hts)⟩
  have hb := localized_source_holder_norm_by_first_norm_of_controlNorm G H C U ha u f jet hz hj hf heq φ
    (fun I => (hword I z t s ht hts hhalf hgap).trans_lt ENNReal.ofReal_lt_top)
  obtain ⟨hzero, hsecond⟩ := hcoeff z t s ht hts hhalf hgap
  rw [frozen_holderENorm_eq_control_norm G driftWeight H.fields C,
    frozen_holderENorm_eq_control_norm G driftWeight H.fields C]
  exact hb.trans (add_le_add (mul_le_mul' hzero le_rfl) (mul_le_mul' hsecond le_rfl))

end RothschildStein.H3
