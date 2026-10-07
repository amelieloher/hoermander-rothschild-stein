-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H3.EuclideanInversionDifferential

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public section
noncomputable section
open Set
namespace RothschildStein.H3
variable {N : ℕ} (G : HomogeneousGroup N)

/-- Reflection multiplies the actual Euclidean gradient
maximum by at most the source's Euclidean inversion constant c_iota. -/
theorem euclideanGradientSphereBound_reflection
    (ν : G2.HomogeneousNorm G) (hsym : ν.Symmetric)
    {f : (Fin N → ℝ) → ℝ} (hf : ContDiffOn ℝ 1 f {0}ᶜ) :
    euclideanGradientSphereBound ν (f ∘ G.inv) ≤
      euclideanInversionSphereBound G ν * euclideanGradientSphereBound ν f := by
  have hfg := reflected_contDiffOn_C1 G hf
  obtain ⟨x, hx, he⟩ := (euclideanGradientSphereBound_properties ν.gauge hfg).2.1
  have hx0 : x ≠ 0 := by
    intro h
    rw [h, (ν.gauge.2.2.1 0).mpr rfl] at hx
    norm_num at hx
  have hix : ν (G.inv x) = 1 := (hsym x).trans hx
  have hdf := (euclideanGradientSphereBound_properties ν.gauge hf).2.2 (G.inv x) hix
  have hdi := (euclideanInversionSphereBound_properties G ν.gauge).2 x hx
  rw [← he, reflected_euclideanDifferential G hf hx0]
  exact ((euclideanDifferential f (G.inv x)).opNorm_comp_le
    (euclideanInversionDifferential G x)).trans
      ((mul_le_mul hdf hdi (norm_nonneg _)
        (euclideanGradientSphereBound_properties ν.gauge hf).1).trans_eq (mul_comm _ _))

/-- The Euclidean gradient maximum is bounded by sqrt(N) Λ₁. -/
theorem euclideanGradientSphereBound_le_kernelDerivativeBound
    {ν T : (Fin N → ℝ) → ℝ} (hν : G.IsHomogeneousGauge ν)
    (hT : ContDiffOn ℝ (⊤ : ℕ∞) T {0}ᶜ) :
    euclideanGradientSphereBound ν T ≤ Real.sqrt N * kernelDerivativeBound ν T 1 := by
  obtain ⟨x, hx, he⟩ :=
    (euclideanGradientSphereBound_properties hν (hT.of_le (by simp))).2.1
  rw [← he]
  exact euclideanDifferential_norm_le_kernelDerivativeBound hν hT hx

end RothschildStein.H3
