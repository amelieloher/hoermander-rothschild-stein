-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H3.CutoffWordHolderFiniteness
public import RothschildStein.H3.FrozenCutoffIntrinsicJets
public import RothschildStein.H3.CutoffHolderPower
public import RothschildStein.H3.ControlDistanceGeometry
public import RothschildStein.H3.QuasiballDomain

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public section
noncomputable section
open Set TopologicalSpace
open scoped ENNReal NNReal
namespace RothschildStein.H3

/-- Localization by the actual smooth quasi-ball cutoff
produces global compact fixed Hölder data of every fixed weighted order.
The input is only local; its exterior values are unrestricted. -/
theorem quasiball_cutoff_holder_membership_of_controlNorm {N q : ℕ}
    (G : HomogeneousGroup N) (H : H1.StandingHypotheses G q)
    (C : G2.ControlNormConclusion G driftWeight H.fields)
    (ν : G2.HomogeneousNorm G) (hν : ν.Smooth)
    (x₀ : Fin N → ℝ) {t s : ℝ} (ht : 0 < t) (hts : t < s) (hhalf : s / 2 ≤ t)
    (k : ℕ) {a : ℝ≥0} (ha : 0 < a) (ha1 : (a : ℝ) ≤ 1)
    (u : (Fin N → ℝ) → ℝ)
    (hu : memHolderX driftWeight H.fields (controlDistance univ driftWeight H.fields)
      (quasiballDomain G ν x₀ s) k a u) :
    memHolderX driftWeight H.fields (controlDistance univ driftWeight H.fields) ⊤ k a
      (fun x => u x * smoothQuasiballCutoff G ν x₀ t s x) ∧
    HasCompactSupport (fun x => u x * smoothQuasiballCutoff G ν x₀ t s x) := by
  classical
  let U := quasiballDomain G ν x₀ s
  let D := controlDistanceGeometry_of_controlNorm G driftWeight H.fields C
  let φ : TestFunction U ℝ (⊤ : ℕ∞) :=
    ⟨smoothQuasiballCutoff G ν x₀ t s,
      smoothQuasiballCutoff_contDiff G ν hν x₀ ht hts,
      smoothQuasiballCutoff_compact G ν x₀ hts,
      (smoothQuasiballCutoff_tsupport G ν x₀ hts).trans
        (intermediate_quasiball_subset G ν x₀ hts)⟩
  obtain ⟨jet, hzero, hjet, hJ⟩ := exists_frozen_cutoff_intrinsic_jets ⊤ U D
    (subset_univ _) driftWeight H.fields (fun i => H.fields_smooth G i) k ha hu φ
  obtain ⟨B, _hB, hB⟩ := exists_quasiball_cutoff_word_holder_power_constants G H C ν hν
    ha1 (sub_pos.mpr hts)
  have hφ (I : List (Fin (q + 1))) :
      holderENorm (controlDistance univ driftWeight H.fields) a univ
        (wordDerivative H.fields I φ) < ⊤ := by
    rw [frozen_holderENorm_eq_control_norm G driftWeight H.fields C]
    exact (hB I x₀ t s ht hts hhalf le_rfl).trans_lt ENNReal.ofReal_lt_top
  let J := fun I => S.leibnizWordValue H.fields I jet φ
  have hn (I : List (Fin (q + 1))) (hI : wordWeight (driftWeight (q := q)) I ≤ k) :
      holderENorm (controlDistance univ driftWeight H.fields) a univ (J I) < ⊤ :=
    leibniz_word_holder_finite_of_controlNorm G H C U a I jet φ
      (fun L hL => (hjet L ((S.wordWeight_sublist_le driftWeight hL).trans hI)).2)
      (fun L _ => hφ L)
  have hw0 : wordWeight (driftWeight (q := q)) [] ≤ k := by simp [wordWeight]
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · change holderENorm (controlDistance univ driftWeight H.fields) a univ
      (fun x => u x * φ x) < ⊤
    rw [← hJ.1]
    exact hn [] hw0
  · intro I hI
    have hi := (S.mem_wordFamily_iff driftWeight k I).mp hI
    exact ⟨J I, (hJ.2 I hi).1, hn I hi⟩
  · have hh := (hJ.2 [] hw0).2.2.1
    rw [hJ.1] at hh
    exact hh

end RothschildStein.H3
