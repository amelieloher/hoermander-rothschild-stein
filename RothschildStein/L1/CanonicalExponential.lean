-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module
public import RothschildStein.L1.CanonicalChartData
@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set Metric
namespace RothschildStein.L1
namespace CanonicalFrameChartData
variable {N : ℕ} {Ω : Set (Fin N → ℝ)}
variable {Y : Fin N → (Fin N → ℝ) → (Fin N → ℝ)} {x : Fin N → ℝ}

/-- The actual time-rescaled trajectory whose time-one endpoint is the
canonical exponential of the constant frame combination. -/
def exponentialCurve (D : CanonicalFrameChartData Ω Y x) (η u : Fin N → ℝ)
    (t : ℝ) : Fin N → ℝ := D.flow ((D.time⁻¹ • u,η),D.time*t)

/-- The canonical trajectory has the required actual initial point. -/
theorem exponentialCurve_zero (D : CanonicalFrameChartData Ω Y x)
    (η u : Fin N → ℝ) (hη : η ∈ ball x D.radius) (hu : u ∈ ball 0 D.radius) :
    D.exponentialCurve η u 0 = η := by
  simpa only [exponentialCurve,mul_zero] using
    (D.flow_ode (D.time⁻¹ • u,η) (D.coefficients (η,u) ⟨hη,hu⟩).1).1

/-- The constructed canonical map is the actual time-one endpoint. -/
theorem exponentialCurve_one (D : CanonicalFrameChartData Ω Y x) (η u : Fin N → ℝ) :
    D.exponentialCurve η u 1 = canonicalFrameMap D.time D.flow (η,u) := by
  simp only [exponentialCurve,mul_one,canonicalFrameMap]

/-- The rescaled trajectory solves the actual constant-frame ODE. -/
theorem exponentialCurve_hasDerivAt (D : CanonicalFrameChartData Ω Y x)
    (η u : Fin N → ℝ) (hη : η ∈ ball x D.radius) (hu : u ∈ ball 0 D.radius)
    {t : ℝ} (ht : D.time*t ∈ Ioo (-D.timeRadius) D.timeRadius) :
    HasDerivAt (D.exponentialCurve η u) (frameCoefficientField Y (u,D.exponentialCurve η u t)) t := by
  have hp := (D.coefficients (η,u) ⟨hη,hu⟩).1
  have hd := ((D.flow_ode (D.time⁻¹ • u,η) hp).2 (D.time*t) ht).1.scomp t
    ((hasDerivAt_id t).const_mul D.time)
  have he : D.time • frameCoefficientField Y (D.time⁻¹ • u,D.exponentialCurve η u t) =
      frameCoefficientField Y (u,D.exponentialCurve η u t) := by
    rw [← frameCoefficientField_smul,smul_smul,mul_inv_cancel₀ (ne_of_gt D.time_pos),one_smul]
  simp only [Function.comp_def,mul_one] at hd
  change HasDerivAt (D.exponentialCurve η u)
    (D.time • frameCoefficientField Y (D.time⁻¹ • u,D.exponentialCurve η u t)) t at hd
  rw [he] at hd
  exact hd

/-- The actual exponential trajectory stays in the spatial domain. -/
theorem exponentialCurve_mem (D : CanonicalFrameChartData Ω Y x)
    (η u : Fin N → ℝ) (hη : η ∈ ball x D.radius) (hu : u ∈ ball 0 D.radius)
    {t : ℝ} (ht : D.time*t ∈ Ioo (-D.timeRadius) D.timeRadius) : D.exponentialCurve η u t ∈ Ω :=
  ((D.flow_ode (D.time⁻¹ • u,η) (D.coefficients (η,u) ⟨hη,hu⟩).1).2 (D.time*t) ht).2
end CanonicalFrameChartData
end RothschildStein.L1
