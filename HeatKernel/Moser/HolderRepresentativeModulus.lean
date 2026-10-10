-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Moser.HolderContinuousRepresentative

/-! Preservation of the quantitative Hölder modulus under continuous extension. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
open MeasureTheory Set
open scoped NNReal
namespace HeatKernel

/-- A continuous extension retains the same Hölder constant and exponent.
The two-point inequality is closed on the product of the ambient space with itself. -/
theorem dist_le_of_continuous_extension_holderOnWith
    {α : Type*} [PseudoMetricSpace α] {s : Set α} {u v : α → ℝ} {C r : ℝ≥0}
    (hs : Dense s) (hv : Continuous v) (he : EqOn v u s)
    (hu : HolderOnWith C r u s) (x y : α) :
    dist (v x) (v y) ≤ (C : ℝ) * dist x y ^ (r : ℝ) := by
  have hclosed : IsClosed {z : α × α |
      dist (v z.1) (v z.2) ≤ (C : ℝ) * dist z.1 z.2 ^ (r : ℝ)} :=
    isClosed_le ((hv.comp continuous_fst).dist (hv.comp continuous_snd))
      (continuous_const.mul ((Real.continuous_rpow_const r.coe_nonneg).comp
        (continuous_fst.dist continuous_snd)))
  have hsub : s ×ˢ s ⊆ {z : α × α |
      dist (v z.1) (v z.2) ≤ (C : ℝ) * dist z.1 z.2 ^ (r : ℝ)} := by
    intro z hz
    change dist (v z.1) (v z.2) ≤ _
    rw [he hz.1, he hz.2]
    exact hu.dist_le hz.1 hz.2
  exact closure_minimal hsub hclosed ((hs.prod hs) (x, y))

/-- Hölder control on a full-measure dense set supplies a continuous
representative with its original quantitative modulus on the entire space. -/
theorem exists_continuous_representative_with_holder_modulus
    {α : Type*} [PseudoMetricSpace α] [MeasurableSpace α]
    (μ : Measure α) [μ.IsOpenPosMeasure] {s : Set α} {u : α → ℝ} {C r : ℝ≥0}
    (hfull : ∀ᵐ x ∂μ, x ∈ s) (hr : 0 < r) (hu : HolderOnWith C r u s) :
    ∃ v : α → ℝ, Continuous v ∧ v =ᵐ[μ] u ∧
      ∀ x y, dist (v x) (v y) ≤ (C : ℝ) * dist x y ^ (r : ℝ) := by
  have hs := μ.dense_of_ae hfull
  obtain ⟨v, hv, he, hae⟩ :=
    exists_uniformContinuous_representative_of_holderOnWith μ hs hfull hr hu
  exact ⟨v, hv.continuous, hae,
    dist_le_of_continuous_extension_holderOnWith hs hv.continuous he hu⟩

end HeatKernel
