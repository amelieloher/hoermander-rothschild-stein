-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.G2.AnalyticStructure
public import RothschildStein.G2.Quasidistance
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
open Set
attribute [local irreducible] RothschildStein.HomogeneousGroup.inv RothschildStein.HomogeneousGroup.mul
namespace RothschildStein.H3
variable {N : ℕ} (G : HomogeneousGroup N)

/-- The kernel obtained from an arbitrary scalar cutoff and
homogeneous convolution kernel, in the product convention of H2. -/
def cutoffGroupKernel (χ T : (Fin N → ℝ) → ℝ) (x y : Fin N → ℝ) : ℝ :=
  χ (G.mul (G.inv y) x) * T (G.mul (G.inv y) x)

/-- Punctured continuity suffices for measurability of the
actual truncated kernel, regardless of the chosen value at the identity. -/
theorem cutoffGroupKernel_measurable {χ T : (Fin N → ℝ) → ℝ}
    (hχ : Measurable χ) (hT : ContinuousOn T {0}ᶜ) :
    Measurable (fun p : (Fin N → ℝ) × (Fin N → ℝ) =>
      cutoffGroupKernel G χ T p.1 p.2) := by
  have hprod : Continuous (fun p : (Fin N → ℝ) × (Fin N → ℝ) =>
      G.mul (G.inv p.2) p.1) :=
    (G2.continuous_mul G).comp
      (((G2.continuous_inv G).comp continuous_snd).prodMk continuous_fst)
  exact (hχ.comp hprod.measurable).mul
    ((measurable_of_continuousOn_compl_singleton 0 hT).comp hprod.measurable)

/-- The kernel vanishes when the relative group coordinate
lies beyond the cutoff radius, including arbitrary diagonal conventions. -/
theorem cutoffGroupKernel_eq_zero {χ T ν : (Fin N → ℝ) → ℝ} {R : ℝ}
    (hχ : ∀ z, R < ν z → χ z = 0) (x y : Fin N → ℝ)
    (hxy : R < G2.gaugeDistance G ν x y) : cutoffGroupKernel G χ T x y = 0 := by
  unfold cutoffGroupKernel
  rw [hχ _ hxy, zero_mul]

end RothschildStein.H3
