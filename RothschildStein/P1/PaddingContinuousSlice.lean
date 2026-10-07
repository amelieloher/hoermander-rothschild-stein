-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.P1.PaddingDistributionDescent
public import RothschildStein.P2.SmoothingRegularity

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
open Set MeasureTheory TopologicalSpace
open scoped ENNReal
namespace RothschildStein.P1

/-- When the padded representative is continuous on the
cylinder, every fixed slice represents the original arbitrary distribution.
Averaging equals restriction at every base point, rather than only almost
everywhere in the full product (BB p. 542, dimension descent). -/
theorem paddingDistributionTensor_continuous_slice_represents {n d : ℕ}
    (Ω : Opens (Fin n → ℝ)) (J : Opens (Fin d → ℝ))
    (hJ : volume (J : Set (Fin d → ℝ)) ≠ ⊤)
    (η : _root_.TestFunction J ℝ ⊤) (hη : ∫ z, η z = 1)
    (T : Distribution Ω ℝ (⊤ : ℕ∞))
    (v : (Fin (n + d) → ℝ) → ℝ)
    (hv : LocallyIntegrableOn v (P2.cylinder Ω J : Set (Fin (n + d) → ℝ)) volume)
    (hT : paddingDistributionTensorOneCLM Ω (P2.cylinder Ω J)
      (padding_cylinder_subset_base Ω J) T =
      Distribution.ofFun (P2.cylinder Ω J) v volume (⊤ : ℕ∞))
    (hc : ContinuousOn v (P2.cylinder Ω J : Set (Fin (n + d) → ℝ)))
    (z : Fin d → ℝ) (hz : z ∈ (J : Set (Fin d → ℝ))) :
    representsDistribution Ω T (fun x => v (joinPoint x z)) := by
  obtain ⟨hrep, hae⟩ := paddingDistributionTensor_descent Ω J hJ η hη T v hv hT
  have he : (P2.fiberAvg v η) =ᵐ[volume.restrict (Ω : Set (Fin n → ℝ))]
      fun x => v (joinPoint x z) := by
    filter_upwards [ae_restrict_mem Ω.isOpen.measurableSet] with x hx
    exact P2.fiberAvg_eq_slice hc hae hη hx hz
  refine ⟨LocallyIntegrableOn.congr he hrep.1, ?_⟩
  exact hrep.2.trans (Distribution.ofFun_congr_ae he)

end RothschildStein.P1
