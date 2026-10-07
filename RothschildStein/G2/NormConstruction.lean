-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.G2.SmoothGauge
public import RothschildStein.G2.EuclideanComparison
public import RothschildStein.G2.Foundation

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
namespace RothschildStein.G2
variable {N : ℕ} {G : HomogeneousGroup N}

/-- Every homogeneous gauge is a homogeneous norm: the common constant
is provided by compactness (BB Prop 3.9, pp. 99–100). -/
def normOfGauge (ν : (Fin N → ℝ) → ℝ) (hν : G.IsHomogeneousGauge ν) : HomogeneousNorm G := by
  let h := gauge_norm_bounds_of_groupIdentities (fun _ ht x => inv_dilate G ht x) hν
  exact ⟨ν, hν, Classical.choose h, (Classical.choose_spec h).1,
    (Classical.choose_spec h).2.1, (Classical.choose_spec h).2.2⟩

/-- The common-multiple polynomial gauge is a homogeneous norm (BB Proposition 3.10, pp. 100–101; Remark 11.35, p. 578). -/
def smoothNorm (G : HomogeneousGroup N) : HomogeneousNorm G :=
  normOfGauge _ (isHomogeneousGauge_smoothGauge G)

/-- The common-multiple polynomial norm is smooth away from zero (BB pp. 100–101). -/
theorem smoothNorm_smooth (G : HomogeneousGroup N) : (smoothNorm G).Smooth :=
  contDiffOn_smoothGauge G

end RothschildStein.G2
