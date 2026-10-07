-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H1.LocalizedL1Bound
public import RothschildStein.H1.NestedCutoffs
public import Mathlib.MeasureTheory.Integral.IntegralEqImproper
public import Mathlib.Topology.Compactness.SigmaCompact

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public section
noncomputable section
open Set MeasureTheory TopologicalSpace Filter
open scoped Topology
namespace RothschildStein.H1
variable {N : ℕ}

/-- Compact exhaustion completes the order-zero to L¹ argument.
The representative need only be smooth on the open domain. -/
theorem integrableOn_of_smooth_orderZero_representation
    (Ω : Opens (Fin N → ℝ)) {γ : (Fin N → ℝ) → ℝ}
    (hγ : ContDiffOn ℝ (⊤ : ℕ∞) γ (Ω : Set (Fin N → ℝ)))
    (T : TestFunction Ω ℝ (⊤ : ℕ∞) →ₗ[ℝ] ℝ)
    {C : ℝ} (hC : 0 ≤ C)
    (hbound : ∀ φ, |T φ| ≤ C * ‖(TestFunction.toBoundedContinuousFunctionCLM ℝ) φ‖)
    (hrep : ∀ φ : TestFunction Ω ℝ (⊤ : ℕ∞), (∫ x, γ x * φ x) = T φ) :
    IntegrableOn γ (Ω : Set (Fin N → ℝ)) := by
  have lcΩ : LocallyCompactSpace Ω := Ω.isOpen.locallyCompactSpace
  let K (n : ℕ) : Set (Fin N → ℝ) := Subtype.val '' compactCovering Ω n
  have hK (n : ℕ) : IsCompact (K n) := (isCompact_compactCovering Ω n).image continuous_subtype_val
  have hKΩ (n : ℕ) : K n ⊆ (Ω : Set (Fin N → ℝ)) := by
    rintro x ⟨y, _, rfl⟩
    exact y.2
  have hcover : AECover (volume.restrict (Ω : Set (Fin N → ℝ))) atTop K := by
    refine ⟨?_, fun n => (hK n).measurableSet⟩
    filter_upwards [ae_restrict_mem Ω.isOpen.measurableSet] with x hx
    obtain ⟨n, hn⟩ := exists_mem_compactCovering (⟨x, hx⟩ : Ω)
    filter_upwards [eventually_ge_atTop n] with m hm
    exact ⟨⟨x, hx⟩, compactCovering_subset Ω hm hn, rfl⟩
  apply hcover.integrable_of_integral_norm_bounded C
  · intro n
    change Integrable γ ((volume.restrict (Ω : Set (Fin N → ℝ))).restrict (K n))
    rw [Measure.restrict_restrict_of_subset (hKΩ n)]
    exact (hγ.continuousOn.mono (hKΩ n)).integrableOn_compact (μ := volume) (hK n)
  · apply Eventually.of_forall
    intro n
    rw [Measure.restrict_restrict_of_subset (hKΩ n)]
    obtain ⟨χ, W, _, hKW, hone, hb⟩ := exists_test_eq_one_near_compact Ω (hK n) (hKΩ n)
    have hi : Integrable (fun x => χ x * |γ x|) := by
      simpa only [smul_eq_mul, Real.norm_eq_abs] using χ.integrable_smul
        (hγ.continuousOn.locallyIntegrableOn Ω.isOpen.measurableSet).norm
    calc
      (∫ x in K n, ‖γ x‖) = ∫ x in K n, χ x * |γ x| := by
        apply setIntegral_congr_fun (hK n).measurableSet
        intro x hx
        change ‖γ x‖ = χ x * |γ x|
        rw [hone x (hKW hx), one_mul, Real.norm_eq_abs]
      _ ≤ ∫ x, χ x * |γ x| := setIntegral_le_integral hi
        (ae_of_all _ fun x => mul_nonneg (hb x).1 (abs_nonneg _))
      _ ≤ C := integral_cutoff_abs_le_orderZero_bound Ω hγ T hC hbound hrep χ hb

end RothschildStein.H1
