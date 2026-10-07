-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.G2.FiniteTransposeIdentity
public import RothschildStein.G2.HomogeneousDivergence

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
namespace RothschildStein.H1
variable {N : ℕ} (G : HomogeneousGroup N)

/-- Step 1: the transpose of a smooth differential operator
of strictly positive homogeneous degree annihilates constants.
Smoothness across the origin is essential (BB Corollary 6.31, p. 280). -/
theorem differentialTranspose_one_eq_zero
    (P : SmoothDifferentialOperator N) {k : ℝ} (hk : 0 < k)
    (hP : P.IsHomogeneous G k) :
    G2.differentialTranspose P (fun _ => (1 : ℝ)) = 0 := by
  have hs := G2.differentialTranspose_preservesSmooth P (fun _ => (1 : ℝ)) contDiff_const
  apply G2.continuous_negative_homogeneous_zero G _ hs.continuous k hk
  intro t ht x
  have h := G2.differentialTranspose_homogeneous G P k hP (fun _ => (1 : ℝ)) contDiff_const t ht x
  simpa only [Function.comp_def] using h

end RothschildStein.H1
