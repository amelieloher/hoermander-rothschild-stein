-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.Definitions.driftWeight
public import RothschildStein.H3.ControlDistanceGeometry
public import RothschildStein.S.IntrinsicWeakHolderExport
public import RothschildStein.S.WeakHolderToIntrinsic
public import RothschildStein.S.HolderArithmetic
public import RothschildStein.S.DistanceMetricLaws
public import RothschildStein.H1.Standing

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public section
noncomputable section
open Set TopologicalSpace
open scoped ENNReal NNReal
namespace RothschildStein.H3

/-- Addition preserves the complete fixed intrinsic Holder
class, using the same weighted words and ambient distance. -/
theorem memHolderX_add_of_controlNorm {N q : ℕ}
    (G : HomogeneousGroup N) (H : H1.StandingHypotheses G q)
    (C : G2.ControlNormConclusion G driftWeight H.fields)
    (U : Opens (Fin N → ℝ)) (k : ℕ) {a : ℝ≥0} (ha : 0 < a)
    {f g : (Fin N → ℝ) → ℝ}
    (hf : memHolderX driftWeight H.fields (controlDistance univ driftWeight H.fields) U k a f)
    (hg : memHolderX driftWeight H.fields (controlDistance univ driftWeight H.fields) U k a g) :
    memHolderX driftWeight H.fields (controlDistance univ driftWeight H.fields) U k a
      (fun x => f x + g x) := by
  let D := controlDistanceGeometry_of_controlNorm G driftWeight H.fields C
  have hx := fun i => (H.fields_smooth G i).contDiffOn (s := (U : Set (Fin N → ℝ)))
  have hsep : ∀ x ∈ (U : Set (Fin N → ℝ)), ∀ y ∈ (U : Set (Fin N → ℝ)), D.d x y = 0 → x = y :=
    fun x _ y _ he => congrArg Subtype.val ((D.distance_eq_zero_iff ⟨x, by simp⟩ ⟨y, by simp⟩).mp he)
  have hadd {v w : (Fin N → ℝ) → ℝ}
      (hv : holderENorm D.d a (U : Set (Fin N → ℝ)) v < ⊤)
      (hw : holderENorm D.d a (U : Set (Fin N → ℝ)) w < ⊤) :
      holderENorm D.d a (U : Set (Fin N → ℝ)) (fun x => v x + w x) < ⊤ :=
    (RothschildStein.S.holderENorm_add_le D.d a (U : Set (Fin N → ℝ))
      (show 0 < (a : ℝ) from ha) hsep v w hv hw).trans_lt (ENNReal.add_lt_top.mpr ⟨hv, hw⟩)
  have hf' := RothschildStein.S.memWeakHolderX_of_memHolderX ⊤ U D (subset_univ _)
    driftWeight H.fields hx k (show 0 < (a : ℝ) from ha) hf
  have hg' := RothschildStein.S.memWeakHolderX_of_memHolderX ⊤ U D (subset_univ _)
    driftWeight H.fields hx k (show 0 < (a : ℝ) from ha) hg
  apply RothschildStein.S.memHolderX_of_memWeakHolderX ⊤ U D (subset_univ _)
    driftWeight H.fields hx k (show 0 < (a : ℝ) from ha)
  refine ⟨hadd hf'.1 hg'.1, ?_⟩
  intro I hI
  obtain ⟨v, hv, hvn⟩ := hf'.2 I hI
  obtain ⟨w, hw, hwn⟩ := hg'.2 I hI
  exact ⟨fun x => v x + w x, RothschildStein.S.hasWeakWordDeriv_add H.fields U hx hv hw,
    hadd hvn hwn⟩

end RothschildStein.H3
