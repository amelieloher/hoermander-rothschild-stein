-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.G1.SmoothDependenceGlobalFamily
public import RothschildStein.G1.SmoothDependenceSignedVariation

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set Filter
open scoped Topology NNReal

namespace RothschildStein.G1

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]

/-- Construct and identify the full first-variation family
on a prescribed bounded cylinder. No initial-data derivative is assumed;
the independently constructed fundamental solutions supply it
(BB Proposition 1.2, p. 3). -/
theorem exists_initial_variation_family
    {Ω U : Set E} (hΩ : IsOpen Ω) (hU : IsOpen U)
    {Z : E → E} (hZ : ContDiffOn ℝ 1 Z Ω)
    {Φ : E → ℝ → E} {T B : ℝ} (hT : 0 < T) {K : ℝ≥0} (hB : 0 ≤ B)
    (hc : ContinuousOn (fun p : E × ℝ => Φ p.1 p.2) (U ×ˢ Icc (-T) T))
    (hsol : ∀ x ∈ U, ∀ t ∈ Icc (-T) T, HasDerivAt (Φ x) (Z (Φ x t)) t)
    (hinit : ∀ x ∈ U, Φ x 0 = x)
    (hmem : ∀ x ∈ U, ∀ t ∈ Icc (-T) T, Φ x t ∈ Ω)
    (hLip : ∀ x ∈ U, ∀ y ∈ U, ∀ t ∈ Icc (-T) T,
      ‖Φ y t - Φ x t‖ ≤ B * ‖y - x‖)
    (hK : ∀ x ∈ U, ∀ t ∈ Icc (-T) T, ‖fderiv ℝ Z (Φ x t)‖ ≤ K) :
    ∃ J : (E × ℝ) → E →L[ℝ] E,
      ContinuousOn J (U ×ˢ Ioo (-T) T) ∧
      ∀ x ∈ U, J (x, 0) = ContinuousLinearMap.id ℝ E ∧
        ∀ t ∈ Icc (-T) T,
          HasFDerivAt (fun y => Φ y t) (J (x, t)) x ∧
          HasDerivAt (fun s => J (x, s))
            ((fderiv ℝ Z (Φ x t)).comp (J (x, t))) t := by
  have hcA : ContinuousOn (fun p : E × ℝ => fderiv ℝ Z (Φ p.1 p.2))
      (U ×ˢ Icc (-T) T) :=
    (hZ.continuousOn_fderiv_of_isOpen hΩ le_rfl).comp hc
      (fun p hp => hmem p.1 hp.1 p.2 hp.2)
  obtain ⟨J, hcJ, hJ⟩ := exists_continuous_fundamental_family_on_Icc hU hT hcA hK
  refine ⟨J, hcJ, fun x hx => ⟨(hJ x hx).2.1, ?_⟩⟩
  have he : ∀ᶠ y in 𝓝 x, y ∈ U := hU.mem_nhds hx
  have hcy : ∀ y ∈ U, ContinuousOn (Φ y) (Icc (-T) T) := by
    intro y hy
    exact hc.comp (continuous_const.prodMk continuous_id).continuousOn (fun _ ht => ⟨hy, ht⟩)
  have hpart := flow_hasFDerivAt_initial_of_fundamental_solution_signed hΩ hZ hT.le hB
    (he.mono (fun y hy => hcy y hy))
    (he.mono (fun y hy t ht => hsol y hy t ht))
    (he.mono (fun y hy => hinit y hy)) (hmem x hx)
    (he.mono (fun y hy t ht => hLip x hx y hy t ht))
    (hJ x hx).1.continuousOn
    (fun t ht => ((hJ x hx).2.2 t ht).2) (hJ x hx).2.1
  exact fun t ht => ⟨hpart t ht, ((hJ x hx).2.2 t ht).2⟩

end RothschildStein.G1
