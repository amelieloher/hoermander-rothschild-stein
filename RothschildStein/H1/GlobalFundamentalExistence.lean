-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H1.LocalFundamentalExistence
public import RothschildStein.H1.GlobalFromLocalFunction
public import RothschildStein.H1.KernelAssembly

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public section
noncomputable section
open Set MeasureTheory TopologicalSpace
namespace RothschildStein.H1
variable {N q : ℕ} (G : HomogeneousGroup N)

/-- The source's local cube is stable under positive contractions by
weighted coordinate dilation. -/
theorem localUnitCube_dilate {t : ℝ} (ht : 0 < t) (ht1 : t ≤ 1)
    {x : Fin N → ℝ} (hx : x ∈ (localUnitCube : Opens (Fin N → ℝ))) :
    G.dilate t x ∈ (localUnitCube : Opens (Fin N → ℝ)) := by
  change dist (G.dilate t x) 0 < 1
  rw [dist_zero_right]
  have hxnorm : ‖x‖ < 1 := by
    change dist x 0 < 1 at hx
    simpa only [dist_zero_right] using hx
  apply (pi_norm_lt_iff (by norm_num : (0 : ℝ) < 1)).mpr
  intro j
  change ‖t ^ G.weight j * x j‖ < 1
  rw [norm_mul, Real.norm_of_nonneg (pow_nonneg ht.le _)]
  exact lt_of_le_of_lt (mul_le_of_le_one_left (norm_nonneg _) (pow_le_one₀ ht.le ht1))
    ((norm_le_pi_norm x j).trans_lt hxnorm)

/-- Global fundamental-kernel existence follows once the local
order-zero distribution is represented by a function. -/
theorem StandingHypotheses.exists_globalFundamentalKernel
    (H : StandingHypotheses G q) (hQ : 2 < (G.homogeneousDimension : ℝ)) :
    Nonempty (FundamentalKernel G H) := by
  obtain ⟨T, _, hT⟩ := H.exists_cubeFundamentalDistribution G
  obtain ⟨γ, hi, hs, he⟩ := H.exists_localFundamentalFunction G localUnitCube
    (by change (0 : Fin N → ℝ) ∈ Metric.ball 0 1; simp)
    (fun t ht ht1 x hx => localUnitCube_dilate G ht ht1 hx) T hT
  obtain ⟨F, hF, hsF, heF, hhF⟩ := H.exists_globalFundamental_of_localFunction G hQ
    localUnitCube (by change (0 : Fin N → ℝ) ∈ Metric.ball 0 1; simp)
    hi.integrableOn hs he
  exact ⟨⟨F, hF, hsF, hhF, heF⟩⟩

end RothschildStein.H1
