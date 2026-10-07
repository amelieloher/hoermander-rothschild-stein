-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H3.TypeZeroTruncatedCertificate
public import RothschildStein.H3.KernelBounds
public import RothschildStein.H3.KernelReflectionFirstBound

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public section
noncomputable section
open Set Metric MeasureTheory
namespace RothschildStein.H3

/-- Original and transpose truncations have common constants
linear in the original kernel seminorm; the coefficients depend only on
control geometry and the field frame. -/
theorem exists_typeZero_geometric_truncated_certificates_of_controlNorm {N q : ℕ}
    (G : HomogeneousGroup N)
    {Y : Fin (q + 1) → (Fin N → ℝ) → (Fin N → ℝ)}
    (C : G2.ControlNormConclusion G driftWeight Y)
    (hY : ∀ i, ContinuousOn (Y i) {0}ᶜ)
    (hhomY : ∀ i, G2.IsHomogeneousField G (Y i) (if i = 0 then 2 else 1)) :
    let _metric : MetricSpace (ControlCarrier N) :=
      gaugeMetric G C.norm C.constant_one C.symmetric
    ∃ A S : ℝ, 0 ≤ A ∧ 0 ≤ S ∧
      ∀ k : (Fin N → ℝ) → ℝ, TypeZero G C.norm k →
      TruncatedKernelFacts volume (kernelDerivativeBound C.norm k 1 * A)
        (kernelDerivativeBound C.norm k 1 * S)
        (fun x y : ControlCarrier N => truncatedKernel G C.norm k x y) ∧
      TruncatedKernelFacts volume (kernelDerivativeBound C.norm k 1 * A)
        (kernelDerivativeBound C.norm k 1 * S)
        (fun x y : ControlCarrier N => truncatedKernel G C.norm k y x) := by
  let _metric : MetricSpace (ControlCarrier N) :=
    gaugeMetric G C.norm C.constant_one C.symmetric
  let m := (volume {z : Fin N → ℝ | C.norm z < 1}).toReal
  let D := cutoffKernelSmoothConstant C.norm Y (-(G.homogeneousDimension : ℝ)) 2 1
  let R := max 1 (Real.sqrt N * euclideanInversionSphereBound G C.norm)
  have hm : 0 ≤ m := ENNReal.toReal_nonneg
  have hD : 0 ≤ D := cutoffKernelSmoothConstant_nonneg C.norm Y
    (-(G.homogeneousDimension : ℝ)) (by norm_num) (by norm_num)
  have hR : 1 ≤ R := le_max_left _ _
  refine ⟨m * R, m * D * R, mul_nonneg hm (zero_le_one.trans hR),
    mul_nonneg (mul_nonneg hm hD) (zero_le_one.trans hR), ?_⟩
  intro k hk
  let Λ := kernelDerivativeBound C.norm k 1
  let Λt := kernelDerivativeBound C.norm (fun z => k (G.inv z)) 1
  have hΛ : 0 ≤ Λ := (kernelDerivativeBound_properties C.norm.gauge hk.smooth 1).1
  have hscale : Λ ≤ R * Λ := by
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hR hΛ
  have href : Λt ≤ R * Λ := kernelDerivativeBound_reflection_one G C.norm C.symmetric hk.smooth
  have hAl (L : ℝ) (hL : L ≤ R * Λ) : m * L ≤ Λ * (m * R) := by
    exact (mul_le_mul_of_nonneg_left hL hm).trans_eq (by ring)
  have hSl (L : ℝ) (hL : L ≤ R * Λ) : m * D * L ≤ Λ * (m * D * R) := by
    exact (mul_le_mul_of_nonneg_left hL (mul_nonneg hm hD)).trans_eq (by ring)
  have H := typeZero_truncatedKernelFacts_of_controlNorm G C hY hhomY hk
  have Ht := typeZero_truncatedKernelFacts_of_controlNorm G C hY hhomY
    (hk.reflection G C.symmetric)
  dsimp only at H Ht ⊢
  refine ⟨truncatedKernelFacts_mono_constants H (hAl Λ hscale) (hSl Λ hscale), ?_⟩
  have Ht' := truncatedKernelFacts_mono_constants Ht (hAl Λt href) (hSl Λt href)
  have heq : (fun x y : ControlCarrier N => truncatedKernel G C.norm k y x) =
      (fun x y : ControlCarrier N => truncatedKernel G C.norm (fun z => k (G.inv z)) x y) := by
    funext x y
    exact truncatedKernel_transpose G C.norm C.symmetric k x y
  rw [heq]
  exact Ht'

end RothschildStein.H3
