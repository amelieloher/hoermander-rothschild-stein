-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H3.LocalConvolutionTruncation
public import RothschildStein.G2.Young

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
open Set MeasureTheory Filter
open scoped ENNReal
namespace RothschildStein.H3
open G2
variable {N : ℕ} {G : HomogeneousGroup N}

/-- Local convolution of a positive-type kernel has the precise
Young(p,1,p) bound for every 1≤p≤infinity (BB pp. 346–351). -/
theorem PositiveType.local_convolution_bound {α : ℝ} {T f : (Fin N → ℝ) → ℝ}
    (hT : PositiveType G α T) (ν : HomogeneousNorm G)
    (h1 : ν.c = 1) (hsym : ν.Symmetric) {ρ₁ ρ₂ : ℝ}
    (hρ₁ : 0 < ρ₁) (hρ₂ : 0 < ρ₂) {p : ℝ≥0∞} (hp : 1 ≤ p)
    (hf : MemLp f p volume) (hsupp : ∀ᵐ y ∂volume, ρ₁ ≤ ν y → f y = 0) :
    MemLp (groupConvolution G f T) p (volume.restrict {x | ν x < ρ₂}) ∧
    eLpNorm (groupConvolution G f T) p (volume.restrict {x | ν x < ρ₂}) ≤
      ENNReal.ofReal (kernelSphereBound ν T * ((G.homogeneousDimension : ℝ) *
        (volume {x | ν x < 1}).toReal * (ρ₁ + ρ₂) ^ α / α)) * eLpNorm f p volume := by
  let k := boundedTypeKernel ν T (ρ₁ + ρ₂)
  have hk : MemLp k 1 volume := memLp_one_iff_integrable.mpr
    (hT.boundedKernel_integrable ν.gauge _)
  have he : p⁻¹ + (1 : ℝ≥0∞)⁻¹ = 1 + p⁻¹ := by simp only [inv_one, add_comm]
  have hm := memLp_groupConvolution G hp le_rfl hp he hf hk
  have hEq : groupConvolution G f T =ᵐ[volume.restrict {x | ν x < ρ₂}]
      groupConvolution G f k := by
    filter_upwards [ae_restrict_mem (isOpen_lt ν.gauge.1 continuous_const).measurableSet] with x hx
    exact groupConvolution_eq_boundedKernel ν h1 hsym hsupp hx
  refine ⟨(memLp_congr_ae hEq).mpr (MemLp.mono_measure Measure.restrict_le_self hm), ?_⟩
  rw [eLpNorm_congr_ae hEq]
  calc
    _ ≤ eLpNorm (groupConvolution G f k) p volume :=
      eLpNorm_mono_measure _ Measure.restrict_le_self
    _ ≤ eLpNorm f p volume * eLpNorm k 1 volume :=
      eLpNorm_groupConvolution_le G hp le_rfl hp he hf.aestronglyMeasurable hk.aestronglyMeasurable
    _ ≤ eLpNorm f p volume * ENNReal.ofReal (kernelSphereBound ν T *
        ((G.homogeneousDimension : ℝ) * (volume {x | ν x < 1}).toReal *
          (ρ₁ + ρ₂) ^ α / α)) := mul_le_mul_right
      (hT.boundedKernel_eLpNorm_bound ν.gauge (add_pos hρ₁ hρ₂)) _
    _ = _ := mul_comm _ _

end RothschildStein.H3
