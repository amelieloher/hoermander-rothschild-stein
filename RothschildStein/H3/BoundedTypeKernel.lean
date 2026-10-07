-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H3.PositiveTypeIntegrability
public import Mathlib.MeasureTheory.Function.L1Space.Integrable

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
open Set MeasureTheory
namespace RothschildStein.H3
open G2
variable {N : ℕ} {G : HomogeneousGroup N}

/-- The compactly truncated homogeneous kernel used for Young(p,1,p)
(BB Chapter 8, pp. 346–351). -/
def boundedTypeKernel (ν T : (Fin N → ℝ) → ℝ) (R : ℝ) : (Fin N → ℝ) → ℝ :=
  {x | ν x ≤ R}.indicator T

/-- The truncated kernel is an actual L1 function for every positive type. -/
theorem PositiveType.boundedKernel_integrable {α : ℝ} {T ν : (Fin N → ℝ) → ℝ}
    (hT : PositiveType G α T) (hν : G.IsHomogeneousGauge ν) (R : ℝ) :
    Integrable (boundedTypeKernel ν T R) volume :=
  (integrable_indicator_iff (isClosed_le hν.1 continuous_const).measurableSet).mpr
    ((hT.locallyIntegrable hν).integrableOn_isCompact (isCompact_gauge_le hν R))

/-- The truncated kernel's L1 norm has exactly the coefficient
Λ_{T,0} Q m R^α/α, rather than an unspecified kernel bound (BB p. 346). -/
theorem PositiveType.boundedKernel_eLpNorm_bound {α R : ℝ} {T ν : (Fin N → ℝ) → ℝ}
    (hT : PositiveType G α T) (hν : G.IsHomogeneousGauge ν) (hR : 0 < R) :
    eLpNorm (boundedTypeKernel ν T R) 1 volume ≤ ENNReal.ofReal
      (kernelSphereBound ν T * ((G.homogeneousDimension : ℝ) *
        (volume {x | ν x < 1}).toReal * R ^ α / α)) := by
  have hI := hT.boundedKernel_integrable hν R
  have hset : MeasurableSet {x | ν x ≤ R} := (isClosed_le hν.1 continuous_const).measurableSet
  have hnorm : (fun x => ‖boundedTypeKernel ν T R x‖) =
      {x | ν x ≤ R}.indicator (fun x => |T x|) := by
    funext x
    by_cases hx : ν x ≤ R <;> simp [boundedTypeKernel, hx, Real.norm_eq_abs]
  rw [eLpNorm_one_eq_lintegral_enorm hI.aestronglyMeasurable,
    ← ofReal_integral_norm_eq_lintegral_enorm hI, hnorm, integral_indicator hset]
  exact ENNReal.ofReal_le_ofReal (hT.integral_abs_ball_bound hν hR)

end RothschildStein.H3
