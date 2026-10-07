-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H3.EuclideanSphereBounds
public import RothschildStein.G2.AnalyticStructure
public import RothschildStein.G2.Algebra

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public section
noncomputable section
open Set
namespace RothschildStein.H3
variable {N : ℕ} (G : HomogeneousGroup N)

/-- The actual inversion differential with Euclidean norms
on both domain and codomain. -/
def euclideanInversionDifferential (x : Fin N → ℝ) :
    EuclideanSpace ℝ (Fin N) →L[ℝ] EuclideanSpace ℝ (Fin N) :=
  (coordinateEuclideanEquiv N).symm.toContinuousLinearMap.comp
    ((fderiv ℝ G.inv x).comp (coordinateEuclideanEquiv N).toContinuousLinearMap)

/-- The source's c_iota, the Euclidean operator norm maximum
of the inversion differential on the actual gauge unit sphere. -/
def euclideanInversionSphereBound (ν : (Fin N → ℝ) → ℝ) : ℝ :=
  kernelSphereBound ν (fun x => ‖euclideanInversionDifferential G x‖)

/-- The transferred inversion differential is continuous. -/
theorem euclideanInversionDifferential_continuous :
    Continuous (euclideanInversionDifferential G) :=
  continuous_const.clm_comp
    (((G2.contDiff_inv G).continuous_fderiv (by simp)).clm_comp continuous_const)

/-- The source inversion maximum is finite, nonnegative,
and bounds its actual Euclidean differential at every sphere point. -/
theorem euclideanInversionSphereBound_properties
    {ν : (Fin N → ℝ) → ℝ} (hν : G.IsHomogeneousGauge ν) :
    0 ≤ euclideanInversionSphereBound G ν ∧
      ∀ x, ν x = 1 → ‖euclideanInversionDifferential G x‖ ≤
        euclideanInversionSphereBound G ν := by
  have hp := kernelSphereBound_continuous hν
    (euclideanInversionDifferential_continuous G).norm.continuousOn
  refine ⟨hp.1, fun x hx => ?_⟩
  simpa only [abs_norm, euclideanInversionSphereBound] using hp.2.2 x hx

/-- Inversion preserves the punctured domain. -/
theorem inversion_maps_punctured : MapsTo G.inv ({0}ᶜ : Set (Fin N → ℝ)) {0}ᶜ := by
  intro x hx
  change x ≠ 0 at hx
  change G.inv x ≠ 0
  intro he
  apply hx
  have h := congrArg G.inv he
  simpa only [G2.inv_inv, G2.inv_zero] using h

/-- Reflection preserves the source's punctured C¹ regularity. -/
theorem reflected_contDiffOn_C1 {f : (Fin N → ℝ) → ℝ}
    (hf : ContDiffOn ℝ 1 f {0}ᶜ) : ContDiffOn ℝ 1 (f ∘ G.inv) {0}ᶜ :=
  hf.comp ((G2.contDiff_inv G).of_le (by simp)).contDiffOn (inversion_maps_punctured G)

/-- The reflected Euclidean scalar differential obeys the
actual chain rule through the transferred Euclidean inversion differential. -/
theorem reflected_euclideanDifferential {f : (Fin N → ℝ) → ℝ}
    (hf : ContDiffOn ℝ 1 f {0}ᶜ) {x : Fin N → ℝ} (hx : x ≠ 0) :
    euclideanDifferential (f ∘ G.inv) x =
      (euclideanDifferential f (G.inv x)).comp (euclideanInversionDifferential G x) := by
  have hinvx := inversion_maps_punctured G hx
  have hdf := (hf.contDiffAt (isOpen_compl_singleton.mem_nhds hinvx)).differentiableAt
    (by norm_num)
  have hdi := (G2.contDiff_inv G).differentiable (by simp) |>.differentiableAt (x := x)
  unfold euclideanDifferential euclideanInversionDifferential
  rw [fderiv_comp x hdf hdi]
  ext v
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
    ContinuousLinearEquiv.apply_symm_apply]

end RothschildStein.H3
