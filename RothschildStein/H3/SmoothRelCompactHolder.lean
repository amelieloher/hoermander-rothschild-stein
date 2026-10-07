-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H3.SmoothSourceFrozenHolder
public import RothschildStein.H3.ControlDistanceGeometry
public import RothschildStein.H3.IntrinsicWordInputCongruence
public import RothschildStein.S.TestOperators
public import RothschildStein.S.WeakHolderToIntrinsic
public import RothschildStein.H1.Standing

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public section
noncomputable section
open Set TopologicalSpace
open scoped ENNReal NNReal
namespace RothschildStein.H3

/-- A smooth homogeneous remainder belongs to every fixed
weighted Holder class on a relatively compact interior domain. -/
theorem memHolderX_of_contDiffOn_relCompact_of_controlNorm {N q : ℕ}
    (G : HomogeneousGroup N) (H : H1.StandingHypotheses G q)
    (C : G2.ControlNormConclusion G driftWeight H.fields)
    (Ω U : Opens (Fin N → ℝ))
    (hK : IsCompact (closure (U : Set (Fin N → ℝ))))
    (hKΩ : closure (U : Set (Fin N → ℝ)) ⊆ Ω)
    (k : ℕ) {a : ℝ≥0} (ha : 0 < a) (ha1 : a ≤ 1)
    (f : (Fin N → ℝ) → ℝ) (hf : ContDiffOn ℝ (⊤ : ℕ∞) f (Ω : Set (Fin N → ℝ))) :
    memHolderX driftWeight H.fields (controlDistance univ driftWeight H.fields) U k a f := by
  let D := controlDistanceGeometry_of_controlNorm G driftWeight H.fields C
  obtain ⟨W, hW, hKW, hclW, hcW⟩ :=
    exists_open_between_and_isCompact_closure hK Ω.isOpen hKΩ
  obtain ⟨χ, hχ, _, hs, hone⟩ :=
    exists_contDiff_support_eq_eq_one_iff (n := (⊤ : ℕ∞)) hW hK.isClosed hKW
  let χΩ : TestFunction Ω ℝ (⊤ : ℕ∞) :=
    ⟨χ, hχ, by simpa [HasCompactSupport, tsupport, hs] using hcW,
      by rw [tsupport, hs]; exact hclW⟩
  let b := testMultiplierOn Ω f hf χΩ
  have he : EqOn (b : (Fin N → ℝ) → ℝ) f (U : Set (Fin N → ℝ)) := by
    intro x hx
    change χ x * f x = f x
    rw [(hone x).mp (subset_closure hx), one_mul]
  obtain ⟨R, hR⟩ := b.hasCompactSupport.bddAbove_image C.norm.gauge.1.continuousOn
  have hsupport : tsupport (b : (Fin N → ℝ) → ℝ) ⊆ {x | C.norm x < R + 1} := by
    intro x hx
    have hh := hR ⟨x, hx, rfl⟩
    change C.norm.toFun x < R + 1
    exact hh.trans_lt (by linarith)
  have hn (I : List (Fin (q + 1))) : holderENorm
      (controlDistance univ driftWeight H.fields) a (U : Set (Fin N → ℝ))
      (wordDerivative H.fields I b) < ⊤ := by
    have hsI := RothschildStein.S.tsupport_wordDerivative_subset H.fields I b
    have hcI := b.hasCompactSupport.of_isClosed_subset isClosed_closure hsI
    have hdI : ContDiff ℝ (⊤ : ℕ∞) (wordDerivative H.fields I b) :=
      contDiffOn_univ.mp (RothschildStein.S.contDiffOn_wordDerivative ⊤ H.fields
        (fun i => (H.fields_smooth G i).contDiffOn) I b b.contDiff.contDiffOn)
    exact (RothschildStein.S.holderENorm_mono _ a univ _ (subset_univ _)).trans_lt
      (smooth_source_global_holder_finite_of_controlNorm G H.fields C a ha1 (R + 1) _ hdI hcI
        (hsI.trans hsupport))
  have hb : memHolderX driftWeight H.fields (controlDistance univ driftWeight H.fields) U k a b := by
    apply RothschildStein.S.memHolderX_of_memWeakHolderX ⊤ U D (subset_univ _)
      driftWeight H.fields (fun i => (H.fields_smooth G i).contDiffOn) k (show 0 < (a : ℝ) from ha)
    refine ⟨by simpa only [D, controlDistanceGeometry_of_controlNorm, wordDerivative] using hn [], ?_⟩
    intro I _
    exact ⟨wordDerivative H.fields I b,
      RothschildStein.S.hasWeakWordDeriv_classical U H.fields
        (fun i => (H.fields_smooth G i).contDiffOn) I b b.contDiff.contDiffOn, hn I⟩
  refine ⟨?_, ?_⟩
  · rw [← RothschildStein.S.holderENorm_congr _ a (U : Set (Fin N → ℝ)) _ he]
    exact hb.1
  · intro I hI
    obtain ⟨g, hg, hgn⟩ := hb.2 I hI
    exact ⟨g, intrinsic_word_congr_input H.fields U I he hg, hgn⟩

end RothschildStein.H3
