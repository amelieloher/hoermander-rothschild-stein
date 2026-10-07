-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H3.IntrinsicFirstFrozenEstimate
public import RothschildStein.H3.FrozenCutoffIntrinsicJets
public import RothschildStein.H3.CutoffFirstHolderPlateau
public import RothschildStein.S.GroupControlGeometry

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public section
noncomputable section
open Set MeasureTheory TopologicalSpace
open scoped ENNReal NNReal BigOperators
namespace RothschildStein.H3

/-- The actual local fixed input and an interior plateau test
satisfy compact interpolation on the plateau. The source is the ordered
Leibniz source of a constructed normalized jet family. -/
theorem localized_first_holder_estimate_of_controlNorm {N q : ℕ} (G : HomogeneousGroup N)
    (H : H1.StandingHypotheses G q) (K : H1.FundamentalKernel G H)
    (Hc : G2.ControlNormConclusion G driftWeight H.fields)
    (hQ : 2 < (G.homogeneousDimension : ℝ)) (μ : G2.GroupMollifier G H.norm)
    (ν : G2.HomogeneousNorm G) (hν : ν.Smooth)
    {α : ℝ≥0} (hα : 0 < α) (hα1 : (α : ℝ) < 1) {ρ : ℝ} (hρ : 0 < ρ) :
    ∃ C : ℝ, 0 < C ∧ ∀ z : Fin N → ℝ,
      ∀ U V : Opens (Fin N → ℝ),
      (U : Set (Fin N → ℝ)) ⊆ G2.gaugeBall G Hc.norm z ρ →
      ∀ u : (Fin N → ℝ) → ℝ,
      memHolderX driftWeight H.fields (controlDistance univ driftWeight H.fields)
        U 2 (α : ℝ) u →
      ∀ φ : TestFunction U ℝ (⊤ : ℕ∞), EqOn φ 1 (V : Set (Fin N → ℝ)) →
      ∃ jet : List (Fin (q + 1)) → (Fin N → ℝ) → ℝ,
        jet [] = u ∧
        (∀ I, wordWeight driftWeight I ≤ 2 →
          hasWeakWordDeriv H.fields U I u (jet I) ∧
          holderENorm (controlDistance univ driftWeight H.fields) (α : ℝ)
            (U : Set (Fin N → ℝ)) (jet I) < ⊤) ∧
        ∀ η : ℝ, 0 < η → η < 1 →
        let F := fun y => S.leibnizWordValue H.fields [0] jet φ y +
          ∑ i : Fin q, S.leibnizWordValue H.fields [i.succ, i.succ] jet φ y
        holderXENorm driftWeight H.fields (controlDistance univ driftWeight H.fields)
          V 1 (α : ℝ) u ≤
          ENNReal.ofReal (η * lpNorm F ∞ volume) +
          ENNReal.ofReal (C * η ^ (-(2 * (3 + (G.homogeneousDimension : ℝ)) /
            (1 - (α : ℝ)))) * lpNorm (fun x => u x * φ x) ∞ volume) := by
  obtain ⟨C, hC, hb⟩ := intrinsic_first_holderX_estimate_of_controlNorm G H K Hc hQ μ ν hν hα hα1 hρ
  let D := S.groupControlGeometry_of_controlNorm G driftWeight H.fields Hc ⊤
  refine ⟨C, hC, ?_⟩
  intro z U V hU u hu φ hφ
  obtain ⟨jet, hzero, hj, hJ0, hJ⟩ := exists_frozen_cutoff_intrinsic_jets ⊤ U D
    (subset_univ _) driftWeight H.fields (H.fields_smooth G) 2
    (show 0 < (α : ℝ) from hα) hu φ
  refine ⟨jet, hzero, hj, ?_⟩
  intro η hη hη1
  have hbound := hb z (fun x => u x * φ x)
    (fun I => S.leibnizWordValue H.fields I jet φ) hJ0
    (fun I hI => (hJ I hI).1) (fun I hI => (hJ I hI).2.1)
    (fun I hI => (hJ I hI).2.2.1)
    (fun I hI => ((hJ I hI).2.2.2.trans φ.tsupport_subset).trans hU) η hη hη1
  exact (cutoff_plateau_first_holderNorm_le H.fields
    (controlDistance univ driftWeight H.fields) V (α : ℝ) u φ
    (fun i => S.leibnizWordValue H.fields [i.succ] jet φ) hφ
    (fun i => (hJ _ (by simp [wordWeight, driftWeight])).1)).trans hbound

end RothschildStein.H3
