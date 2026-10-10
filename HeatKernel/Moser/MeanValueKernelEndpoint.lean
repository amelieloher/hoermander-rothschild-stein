-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Geometry.CoordinateBall
public import HeatKernel.Kernel.CompactCylinderBounds
public import HeatKernel.Gaussian.EndpointEssentialMeanValue
import Mathlib.Tactic

/-! # Positive-power mean-value estimates in the kernel endpoint normalization -/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set MeasureTheory Metric RothschildStein
open scoped ENNReal
namespace HeatKernel
set_option backward.isDefEq.respectTransparency false

/-- A continuous positive-time representative has finite quadratic norm on each
Gaussian endpoint cylinder, including when its weak equation is only local. -/
theorem memLp_two_kernel_endpoint_of_continuousOn {N q : ℕ}
    (G : HomogeneousGroup N) (hq : q ≤ N) (hqpos : 0 < q)
    (hspan : bracketSpansOn univ (G.horizontalFields hq))
    (hw : ∀ i : Fin q, G.weight (Fin.castLE hq i) = 1)
    (s r : ℝ) (w : CarnotPoint G hq hqpos hspan)
    (hstart : 0 < s - 7 * r ^ 2 / 2)
    (v : ℝ × (Fin N → ℝ) → ℝ) (hv : ContinuousOn v (Ioi 0 ×ˢ univ)) :
    MemLp v 2 ((volume.restrict (Ioo (s - 7 * r ^ 2 / 2) (s + r ^ 2 / 2))).prod
      ((CarnotPoint.volume G hq hqpos hspan).restrict (ball w (2 * r)))) := by
  let _ : ProperSpace (CarnotPoint G hq hqpos hspan) :=
    CarnotPoint.properSpace G hq hqpos hspan hw
  let J := Icc (s - 7 * r ^ 2 / 2) (s + r ^ 2 / 2)
  let K : Set (Fin N → ℝ) := @closedBall (CarnotPoint G hq hqpos hspan) _ w (2 * r)
  have hcompact : IsCompact (J ×ˢ K) := isCompact_Icc.prod (isCompact_closedBall w (2 * r))
  have hsub : J ×ˢ K ⊆ Ioi 0 ×ˢ univ := fun z hz =>
    ⟨hstart.trans_le hz.1.1, mem_univ _⟩
  have hmem := memLp_two_restrict_of_continuousOn_compact
    (μ := (volume : Measure (ℝ × (Fin N → ℝ)))) hcompact (hv.mono hsub)
  have hsmall : Ioo (s - 7 * r ^ 2 / 2) (s + r ^ 2 / 2) ×ˢ
      (@ball (CarnotPoint G hq hqpos hspan) _ w (2 * r) : Set (Fin N → ℝ)) ⊆ J ×ˢ K :=
    Set.prod_mono Ioo_subset_Icc_self ball_subset_closedBall
  have hresult := hmem.mono_measure (Measure.restrict_mono hsmall le_rfl)
  change MemLp v 2 ((volume.restrict (Ioo (s - 7 * r ^ 2 / 2) (s + r ^ 2 / 2))).prod
    ((volume : Measure (Fin N → ℝ)).restrict
      (@ball (CarnotPoint G hq hqpos hspan) _ w (2 * r))))
  rw [Measure.prod_restrict, ← Measure.volume_eq_prod]
  exact hresult

/-- The normalized essential estimate gives exactly the squared endpoint mean
used by the Gaussian kernel construction. Continuity supplies the initial L² norm;
the essential estimate is the remaining analytic input. -/
theorem kernel_endpoint_mean_value_of_essential_bound {N q : ℕ}
    (G : HomogeneousGroup N) (hq : q ≤ N) (hqpos : 0 < q)
    (hspan : bracketSpansOn univ (G.horizontalFields hq))
    (hw : ∀ i : Fin q, G.weight (Fin.castLE hq i) = 1)
    (s r : ℝ) (w : CarnotPoint G hq hqpos hspan) (hr : 0 < r)
    (hstart : 0 < s - 7 * r ^ 2 / 2)
    (v : ℝ × (Fin N → ℝ) → ℝ) (hv : ContinuousOn v (Ioi 0 ×ˢ univ))
    {C : ℝ} (hC : 0 ≤ C)
    (hbound : eLpNormEssSup v (((volume : Measure ℝ).prod
      (CarnotPoint.volume G hq hqpos hspan)).restrict
        (Ioo (s - r ^ 2 / 2) (s + r ^ 2 / 2) ×ˢ ball w r)) ≤
      ENNReal.ofReal C * eLpNorm v 2
        (ENNReal.ofReal (r ^ 2 * (CarnotPoint.volume G hq hqpos hspan).real (ball w (2 * r)))⁻¹ •
          ((volume.restrict (Ioo (s - 7 * r ^ 2 / 2) (s + r ^ 2 / 2))).prod
            ((CarnotPoint.volume G hq hqpos hspan).restrict (ball w (2 * r)))))) :
    v (s, w) ^ 2 ≤ C ^ 2 /
      (r ^ 2 * (CarnotPoint.volume G hq hqpos hspan).real (ball w (2 * r))) *
        ∫ σ in Ioo (s - 7 * r ^ 2 / 2) (s + r ^ 2 / 2),
          ∫ z in ball w (2 * r), v (σ, z) ^ 2 ∂(CarnotPoint.volume G hq hqpos hspan) := by
  have hinner : Ioo (s - r ^ 2 / 2) (s + r ^ 2 / 2) ×ˢ
      (@ball (CarnotPoint G hq hqpos hspan) _ w r : Set (Fin N → ℝ)) ⊆ Ioi 0 ×ˢ univ := by
    intro z hz
    refine ⟨?_, mem_univ _⟩
    change 0 < z.1
    have hzlo : s - r ^ 2 / 2 < z.1 := hz.1.1
    linarith [sq_nonneg r]
  have hV : 0 < (CarnotPoint.volume G hq hqpos hspan).real (ball w (2 * r)) := by
    change 0 < volume.real (CarnotPoint.coordinateBall G hq hqpos hspan w (2 * r) : Set (Fin N → ℝ))
    rw [CarnotPoint.coordinateBall_eq_horizontalBall, Measure.real]
    exact ENNReal.toReal_pos (ne_of_gt (volume_horizontalBall_pos G hq hqpos hspan w (by positivity)))
      (ne_of_lt (volume_horizontalBall_lt_top G hq hqpos hspan hw w (by positivity)))
  let : SFinite (CarnotPoint.volume G hq hqpos hspan) :=
    (inferInstance : SFinite (volume : Measure (Fin N → ℝ)))
  let : (((volume : Measure ℝ).prod (CarnotPoint.volume G hq hqpos hspan))).IsOpenPosMeasure := by
    change ((volume : Measure (ℝ × (Fin N → ℝ)))).IsOpenPosMeasure
    infer_instance
  exact Gaussian.sq_center_le_endpoint_integral_of_essential_bound
    (CarnotPoint.volume G hq hqpos hspan) s r w hr v (hv.mono hinner)
    (memLp_two_kernel_endpoint_of_continuousOn G hq hqpos hspan hw s r w hstart v hv)
    hC hV hbound

end HeatKernel
