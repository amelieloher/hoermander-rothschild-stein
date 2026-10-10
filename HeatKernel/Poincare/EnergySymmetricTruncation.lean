-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Form.PositivePart
public import HeatKernel.Poincare.EnergyRepresentativeAlgebra
public import HeatKernel.Poincare.SymmetricTruncation

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
open Set Filter MeasureTheory TopologicalSpace RothschildStein
open scoped ENNReal Topology
namespace HeatKernel

attribute [local irreducible] energyGraph

/-- Symmetric truncations belong to the horizontal energy domain; their gradient is
the original gradient restricted to the interval between the two levels. -/
theorem exists_energyGraph_symmetric_truncation {N q : ℕ}
    (X : Fin q → (Fin N → ℝ) → (Fin N → ℝ))
    (hX : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (X i)) (u : energyGraph (N := N) ⊤ X)
    {M : ℝ} (hM : 0 ≤ M) :
    ∃ z : energyGraph (N := N) ⊤ X,
      (z : GradientSpace (N := N) ⊤ q).fst =ᵐ[volume]
        (fun x => max (-M) (min ((u : GradientSpace (N := N) ⊤ q).fst x) M)) ∧
      ∀ i, (z : GradientSpace (N := N) ⊤ q).snd i =ᵐ[volume]
        (fun x => if |(u : GradientSpace (N := N) ⊤ q).fst x| ≤ M then (u : GradientSpace (N := N) ⊤ q).snd i x else 0) := by
  obtain ⟨v, hvf, hvg⟩ := exists_energyGraph_positiveLevel X hX u M hM
  obtain ⟨w, hwf, hwg⟩ := exists_energyGraph_positiveLevel X hX (-u) M hM
  have hnegf := energyInclusion_neg_ae X u
  have hnegg := energyGradient_neg_ae X u
  simp only [energyInclusion_apply, energyGradient_apply] at hnegf hnegg
  refine ⟨u - v + w, ?_, fun i => ?_⟩
  · have hz := energyInclusion_sub_add_ae X u v w
    simp only [energyInclusion_apply] at hz
    filter_upwards [hz, hvf, hwf, hnegf] with x hx hv hw hn
    simp only [Pi.add_apply, Pi.sub_apply] at hx
    simp only [Pi.neg_apply] at hn
    rw [hx, hv, hw, hn, symmetric_truncation_eq_positive_parts hM]
  · have hz := energyGradient_sub_add_ae X u v w i
    simp only [energyGradient_apply] at hz
    filter_upwards [hz, hvg i, hwg i, hnegf, hnegg i] with x hx hv hw hn hng
    simp only [Pi.add_apply, Pi.sub_apply] at hx
    simp only [Pi.neg_apply] at hn hng
    rw [hx, hv, hw, hn, hng]
    exact symmetric_truncation_gradient_identity hM _ _

end HeatKernel
