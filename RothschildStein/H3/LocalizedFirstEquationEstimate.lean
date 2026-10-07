-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H3.LocalizedFirstCoefficientEstimate
public import RothschildStein.H3.FrozenDriftEquationBridge

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public section
noncomputable section
open Set MeasureTheory TopologicalSpace
open scoped ENNReal NNReal BigOperators
namespace RothschildStein.H3

/-- The exact fixed distribution equation identifies the
local selected source with the forcing. The coefficient estimate then
uses only the forcing, input supremum and first-order fixed norm. -/
theorem localized_first_equation_coefficient_estimate_of_controlNorm {N q : ℕ} (G : HomogeneousGroup N)
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
      ∀ f : (Fin N → ℝ) → ℝ,
      hasDistributionEquationWithDrift U H.fields
        (fun i => (H.fields_smooth G i).contDiffOn)
        (Distribution.ofFun U u volume (⊤ : ℕ∞)) f →
      ∀ φ : TestFunction U ℝ (⊤ : ℕ∞), EqOn φ 1 (V : Set (Fin N → ℝ)) →
      ∀ A B : ℝ≥0∞,
      eLpNorm φ ⊤ (volume.restrict (U : Set (Fin N → ℝ))) ≤ 1 →
      (∀ i : Fin q, eLpNorm (fieldDerivative (H.fields i.succ) φ) ⊤
        (volume.restrict (U : Set (Fin N → ℝ))) ≤ A) →
      eLpNorm (sumSquaresWithDrift H.fields φ) ⊤
        (volume.restrict (U : Set (Fin N → ℝ))) ≤ B →
        ∀ η : ℝ, 0 < η → η < 1 →
        holderXENorm driftWeight H.fields (controlDistance univ driftWeight H.fields)
          V 1 (α : ℝ) u ≤
          ENNReal.ofReal η *
            (eLpNorm f ⊤
              (volume.restrict (U : Set (Fin N → ℝ))) +
             B * eLpNorm u ⊤ (volume.restrict (U : Set (Fin N → ℝ))) +
             2 * A * holderXENorm driftWeight H.fields
               (controlDistance univ driftWeight H.fields) U 1 (α : ℝ) u) +
          ENNReal.ofReal (C * η ^ (-(2 * (3 + (G.homogeneousDimension : ℝ)) /
            (1 - (α : ℝ))))) * eLpNorm u ⊤ (volume.restrict (U : Set (Fin N → ℝ))) := by
  obtain ⟨C, hC, hb⟩ := localized_first_coefficient_estimate_of_controlNorm G H K Hc hQ μ ν hν hα hα1 hρ
  let Dgeom := S.groupControlGeometry_of_controlNorm G driftWeight H.fields Hc ⊤
  refine ⟨C, hC, ?_⟩
  intro z U V hU u hu f heq φ hφ A B hn hA hB
  obtain ⟨jet, hzero, hj, hbound⟩ := hb z U V hU u hu φ hφ A B hn hA hB
  let D := holderJetDriftData ⊤ U Dgeom (subset_univ _) H.fields
    (show 0 < (α : ℝ) from hα) u jet hj
  have he := D.operator_ae_eq_of_frozen_equation (by simp)
    (fun i => (H.fields_smooth G i).contDiffOn) f heq
  have heNorm : eLpNorm (fun x => jet [0] x + ∑ i : Fin q, jet [i.succ, i.succ] x) ⊤
      (volume.restrict (U : Set (Fin N → ℝ))) =
      eLpNorm f ⊤ (volume.restrict (U : Set (Fin N → ℝ))) :=
    eLpNorm_congr_ae he
  intro η hη hη1
  have hh := hbound η hη hη1
  rw [heNorm] at hh
  exact hh

end RothschildStein.H3
