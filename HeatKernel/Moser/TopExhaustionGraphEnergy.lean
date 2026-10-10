-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Moser.MeanValueIdentityEnergyBudget

/-! # Measurable spatial gradient energies along graph curves -/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open MeasureTheory TopologicalSpace
namespace HeatKernel

/-- The literal weighted spatial gradient integral along a Bochner L² graph curve
is an integrable scalar function of time. -/
theorem integrable_weighted_graph_gradient_curve
    {α : Type*} [MeasurableSpace α] {μ : Measure α} {N q : ℕ}
    {V : Opens (Fin N → ℝ)} {X : Fin q → (Fin N → ℝ) → (Fin N → ℝ)}
    {η : (Fin N → ℝ) → ℝ} {K : ℝ}
    (hη : AEStronglyMeasurable η volume) (hb : ∀ᵐ x ∂volume, ‖η x‖ ≤ K)
    {v : α → zeroBoundaryGraph V X} (hv : MemLp v 2 μ) :
    Integrable (fun t => ∫ x, ∑ i, (η x *
      (v t : GradientSpace (N := N) ⊤ q).snd i x) ^ 2) μ := by
  have hi := (zeroBoundaryEnergyInclusion V X).comp_memLp' hv
  have he := integrable_coefficientEnergy_curves ⊤ X
    (fun i j z => η z.2 ^ 2 * if i = j then 1 else 0) (sq_nonneg K)
    (fun i j => by
      simpa only [Opens.coe_top, Measure.restrict_univ, Pi.mul_def, Pi.pow_def] using
        (hη.comp_snd.pow 2).mul aestronglyMeasurable_const)
    (fun i j => by
      simp only [Opens.coe_top, Measure.restrict_univ]
      filter_upwards [Measure.quasiMeasurePreserving_snd.ae hb] with z hz
      by_cases hij : i = j
      · simpa only [hij, ite_true, mul_one, norm_pow] using
          pow_le_pow_left₀ (norm_nonneg (η z.2)) hz 2
      · simp only [hij, ite_false, mul_zero, norm_zero]
        exact sq_nonneg K)
    _ _ hi hi
  simp only [square_weighted_identity_coefficientEnergy_eq_integral, Function.comp_apply] at he
  exact he

end HeatKernel
