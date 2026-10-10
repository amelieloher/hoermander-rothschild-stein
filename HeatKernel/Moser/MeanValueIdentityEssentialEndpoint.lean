-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Moser.MeanValueIdentityPositivePowerEndpoint
import Mathlib.Tactic

/-! # Normalized essential mean values on Gaussian endpoint cylinders -/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set MeasureTheory TopologicalSpace RothschildStein
open scoped ENNReal
namespace HeatKernel
set_option backward.isDefEq.respectTransparency false

/-- The identity weak equation gives the normalized essential quadratic mean-value
estimate on the whole inner endpoint cylinder, including its open top time. -/
theorem exists_uniform_identity_kernel_endpoint_essential_mean_value {N q : ℕ}
    (G : HomogeneousGroup N) (hq : q ≤ N) (hqpos : 0 < q)
    (hspan : bracketSpansOn univ (G.horizontalFields hq))
    (hw : ∀ i : Fin q, G.weight (Fin.castLE hq i) = 1) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (s r : ℝ) (w : CarnotPoint G hq hqpos hspan),
      0 < r → 0 < s - 7 * r ^ 2 / 2 →
      ∀ v : ℝ × (Fin N → ℝ) → ℝ,
      ContinuousOn v (Ioi 0 ×ˢ univ) →
      (∀ σ > 0, ∀ z, 0 ≤ v (σ, z)) →
      IsLocalWeakSolution G hq hqpos hw hspan
        (fun _ _ i j => if i = j then 1 else 0)
        ⟨Ioo (s - 7 * r ^ 2 / 2) (s + r ^ 2 / 2), isOpen_Ioo⟩
        ⟨interior (horizontalBall (G.horizontalFields hq) w (2 * r)), isOpen_interior⟩
        (fun σ z => v (σ, z)) →
      eLpNormEssSup v (((volume : Measure ℝ).prod
        (CarnotPoint.volume G hq hqpos hspan)).restrict
          (Ioo (s - r ^ 2 / 2) (s + r ^ 2 / 2) ×ˢ Metric.ball w r)) ≤
        ENNReal.ofReal C * eLpNorm v 2
          (ENNReal.ofReal (r ^ 2 *
            (CarnotPoint.volume G hq hqpos hspan).real (Metric.ball w (2 * r)))⁻¹ •
              ((volume.restrict (Ioo (s - 7 * r ^ 2 / 2) (s + r ^ 2 / 2))).prod
                ((CarnotPoint.volume G hq hqpos hspan).restrict (Metric.ball w (2 * r))))) := by
  obtain ⟨C, hC, hmean⟩ :=
    exists_uniform_identity_kernel_endpoint_positive_power_mean_value G hq hqpos hspan hw
      (p := 2) (by norm_num)
  refine ⟨C, hC, ?_⟩
  intro s r w hr hstart v _hvc hv0 hweak
  simpa only [ENNReal.ofReal_ofNat] using hmean s r w hr hstart v hv0 hweak

end HeatKernel
