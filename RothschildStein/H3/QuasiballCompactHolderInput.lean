-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H3.QuasiballCutoffHolderMembership
public import RothschildStein.H3.IntrinsicWordRestriction
public import RothschildStein.Definitions.memHolderXCompact

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
open Set TopologicalSpace
open scoped NNReal
namespace RothschildStein.H3

/-- The actual localized input satisfies the literal fixed
compact Hölder predicate on the outer quasi-ball. Its closed support
lies strictly inside that ball, before global estimates are applied. -/
theorem quasiball_cutoff_compact_holder_input_of_controlNorm {N q : ℕ}
    (G : HomogeneousGroup N) (H : H1.StandingHypotheses G q)
    (C : G2.ControlNormConclusion G driftWeight H.fields)
    (ν : G2.HomogeneousNorm G) (hν : ν.Smooth)
    (x₀ : Fin N → ℝ) {t s : ℝ} (ht : 0 < t) (hts : t < s) (hhalf : s / 2 ≤ t)
    (k : ℕ) {a : ℝ≥0} (ha : 0 < a) (ha1 : (a : ℝ) ≤ 1)
    (u : (Fin N → ℝ) → ℝ)
    (hu : memHolderX driftWeight H.fields (controlDistance univ driftWeight H.fields)
      (quasiballDomain G ν x₀ s) k a u) :
    memHolderXCompact driftWeight H.fields (controlDistance univ driftWeight H.fields)
      (quasiballDomain G ν x₀ s) k a
      (fun x => u x * smoothQuasiballCutoff G ν x₀ t s x) := by
  let U := quasiballDomain G ν x₀ s
  let f := fun x => u x * smoothQuasiballCutoff G ν x₀ t s x
  obtain ⟨hf, hc⟩ := quasiball_cutoff_holder_membership_of_controlNorm
    G H C ν hν x₀ ht hts hhalf k ha ha1 u hu
  have hs : tsupport f ⊆ (U : Set (Fin N → ℝ)) :=
    tsupport_mul_subset_right.trans ((smoothQuasiballCutoff_tsupport G ν x₀ hts).trans
      (intermediate_quasiball_subset G ν x₀ hts))
  have hclosure : closure ((U : Set (Fin N → ℝ)) ∩ Function.support f) ⊆ tsupport f :=
    closure_mono inter_subset_right
  refine ⟨memHolderX_restrict_intrinsic driftWeight H.fields
    (controlDistance univ driftWeight H.fields) ⊤ U (subset_univ _) k a hf, ?_, ?_⟩
  · exact hc.isCompact.of_isClosed_subset isClosed_closure hclosure
  · exact hclosure.trans hs

end RothschildStein.H3
