-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H3.StandingRegularityInputs
public import RothschildStein.Provider.FundamentalSolutionInputs

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public section
noncomputable section
open Set
namespace RothschildStein.H3

/-- All seven canonical no-drift inputs use the original
horizontal frame and its literal fixed function spaces and equation. -/
theorem groupRegularityInputs_canonical_noDrift {N q : ℕ}
    (G : HomogeneousGroup N) (hq : q ≤ N) (hqpos : 0 < q)
    (hw : ∀ i : Fin q, G.weight (Fin.castLE hq i) = 1)
    (hQ : 3 ≤ G.homogeneousDimension)
    (hspan : bracketSpansOn univ (G.horizontalFields hq))
    (νs : (Fin N → ℝ) → ℝ) (hνs : G.IsHomogeneousGauge νs)
    (hνs_smooth : ContDiffOn ℝ (⊤ : ℕ∞) νs ({0}ᶜ)) :
    Provider.GroupRegularityInputs G noDriftWeight (G.horizontalFields hq)
      (fun Ω T f => hasDistributionEquation Ω (G.horizontalFields hq)
        (fun i => (G.horizontalFields_contDiff hq i).contDiffOn) T f) νs := by
  let H := Provider.horizontalStandingHypotheses G hq hqpos hw hspan νs hνs
  have hQr : 2 < (G.homogeneousDimension : ℝ) := (H1.dimension_gt_two_iff G).mpr hQ
  obtain ⟨K⟩ := (Provider.fundamentalSolutionInputs G hQr).existence H hQr
  let C := standingControlNormConclusion G H
  let D := controlDistanceGeometry_of_controlNorm G driftWeight H.fields C
  have hD : D.d = controlDistance univ noDriftWeight (G.horizontalFields hq) := by
    change controlDistance univ driftWeight (Fin.cases 0 (G.horizontalFields hq)) = _
    funext x y
    exact controlDistance_zero_drift_eq univ (G.horizontalFields hq) x y
  exact groupRegularityInputs_zero_drift G (G.horizontalFields hq) (G.horizontalFields_contDiff hq)
    νs D hD (groupRegularityInputs_standing G H K hQr νs hνs hνs_smooth)

/-- Universal shared no-drift regularity inputs for the exact
original horizontal fields and weights. -/
theorem canonicalNoDriftRegularity_holds : Provider.CanonicalNoDriftRegularity := by
  constructor
  all_goals intro N q G hq hqpos hw hQ hspan νs hνs hνs_smooth hνs_symm
  · exact (groupRegularityInputs_canonical_noDrift G hq hqpos hw hQ hspan νs hνs hνs_smooth).globalLp
  · exact (groupRegularityInputs_canonical_noDrift G hq hqpos hw hQ hspan νs hνs hνs_smooth).compactHolder
  · exact (groupRegularityInputs_canonical_noDrift G hq hqpos hw hQ hspan νs hνs hνs_smooth).localLp
  · exact (groupRegularityInputs_canonical_noDrift G hq hqpos hw hQ hspan νs hνs hνs_smooth).localHolder
  · exact (groupRegularityInputs_canonical_noDrift G hq hqpos hw hQ hspan νs hνs hνs_smooth).lpSolve
  · exact (groupRegularityInputs_canonical_noDrift G hq hqpos hw hQ hspan νs hνs hνs_smooth).quasiball
  · exact (groupRegularityInputs_canonical_noDrift G hq hqpos hw hQ hspan νs hνs hνs_smooth).holderBall

end RothschildStein.H3
