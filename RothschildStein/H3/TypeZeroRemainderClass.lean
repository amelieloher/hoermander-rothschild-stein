-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H3.TypeZeroRemainderCutoff
public import RothschildStein.H3.DiagonalGapFractionalClass
public import RothschildStein.H3.CutoffKernelClass
public import RothschildStein.H3.TypeZero

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public section
noncomputable section
open Set Metric MeasureTheory
namespace RothschildStein.H3

/-- The actual nonsingular radial remainder satisfies the
fractional kernel class of order one, with coefficients linear in Λ₁. -/
theorem typeZero_remainder_fractional_class_of_controlNorm {N q : ℕ}
    (G : HomogeneousGroup N)
    {Y : Fin (q + 1) → (Fin N → ℝ) → (Fin N → ℝ)}
    (C : G2.ControlNormConclusion G driftWeight Y)
    (hY : ∀ i, ContinuousOn (Y i) {0}ᶜ)
    (hhomY : ∀ i, G2.IsHomogeneousField G (Y i) (if i = 0 then 2 else 1))
    {k : (Fin N → ℝ) → ℝ} (hk : TypeZero G C.norm k) :
    let _metric := gaugeMetric G C.norm C.constant_one C.symmetric
    let m := (volume {z : Fin N → ℝ | C.norm z < 1}).toReal
    H2.KernelClass volume univ 1 1 (m * kernelDerivativeBound C.norm k 1)
      (2 * (m * cutoffKernelSmoothConstant C.norm Y (-(G.homogeneousDimension : ℝ)) 3 2 *
        kernelDerivativeBound C.norm k 1))
      (fun x y : ControlCarrier N => cutoffGroupKernel G (typeZeroRemainderCutoff C.norm) k x y) := by
  let _metric := gaugeMetric G C.norm C.constant_one C.symmetric
  obtain ⟨hrange, hcont, hsupp, hgap, hmod⟩ :=
    typeZeroRemainderCutoff_properties G C.norm C.constant_one C.symmetric
  have H := cutoffGroupKernel_kernelClass_of_controlNorm C hY hhomY hk.smooth
    (show (0 : ℝ) ≤ 0 from le_rfl)
    (show (0 : ℝ) ≤ G.homogeneousDimension from Nat.cast_nonneg _)
    (by simpa only [zero_sub] using hk.homogeneous)
    (show (0 : ℝ) < 3 by norm_num) (show (0 : ℝ) ≤ 2 by norm_num)
    hcont.measurable hrange hmod (fun z hz => hsupp z hz.le)
  dsimp only at H ⊢
  apply kernelClass_fractional_of_unit_diagonal_gap G C.norm C.constant_one C.symmetric
    (by simpa only [zero_sub] using H)
  dsimp only
  intro x y hxy
  unfold cutoffGroupKernel
  rw [hgap _ hxy, zero_mul]

end RothschildStein.H3
