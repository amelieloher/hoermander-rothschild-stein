-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Poincare.TranslationPairs
public import Mathlib.MeasureTheory.Measure.Prod

/-! Right Haar invariance for energy integrated along translated paths. -/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open MeasureTheory Set RothschildStein
open scoped ENNReal

namespace HeatKernel

/-- A right translation whose image stays in the energy domain cannot increase its
nonnegative energy integral beyond the integral over that domain. -/
theorem lintegral_rightTranslation_le_of_image_subset {N : ℕ}
    (G : HomogeneousGroup N) (z : Fin N → ℝ) {B U : Set (Fin N → ℝ)}
    (hsub : (fun y => G.mul y z) '' B ⊆ U) (F : (Fin N → ℝ) → ℝ≥0∞) :
    (∫⁻ y in B, F (G.mul y z)) ≤ ∫⁻ y in U, F y := by
  have hm := G2.measurePreserving_rightTranslation G z
  have he := hm.measurable.measurableEmbedding (G2.rightTranslation_bijective G z).injective
  rw [hm.setLIntegral_comp_emb he F B]
  exact lintegral_mono_set hsub

/-- A locally measurable curve may be composed with the second projection of a product
measure and then with a measurable function of the two coordinates. -/
theorem aemeasurable_product_curve {E T V : Type*}
    [MeasurableSpace E] [MeasurableSpace T] [MeasurableSpace V]
    {μ : Measure E} {ν : Measure T} [SFinite ν] {γ : T → V}
    (hγ : AEMeasurable γ ν) {H : E × V → ℝ≥0∞} (hH : Measurable H) :
    AEMeasurable (fun p : E × T => H (p.1, γ p.2)) (μ.prod ν) := by
  have hsnd : AEMeasurable (fun p : E × T => γ p.2) (μ.prod ν) := hγ.comp_snd
  have hfst : AEMeasurable (fun p : E × T => p.1) (μ.prod ν) := measurable_fst.aemeasurable
  exact hH.comp_aemeasurable (hfst.prodMk hsnd)

/-- A measurable group product with a locally measurable curve is measurable for the
restricted product measure. -/
theorem aemeasurable_mul_curve {N : ℕ} (G : HomogeneousGroup N)
    {T : Type*} [MeasurableSpace T] {ν : Measure T} [SFinite ν]
    {B : Set (Fin N → ℝ)} {S : Set T} {γ : T → (Fin N → ℝ)}
    (hγ : AEMeasurable γ (ν.restrict S))
    {F : (Fin N → ℝ) → ℝ≥0∞} (hF : Measurable F) :
    AEMeasurable (fun p : (Fin N → ℝ) × T => F (G.mul p.1 (γ p.2)))
      ((volume.restrict B).prod (ν.restrict S)) :=
  aemeasurable_product_curve hγ (hF.comp (G2.continuous_mul G).measurable)

/-- The energy of translated paths is bounded by parameter measure times the energy
on a common containing domain. This statement uses no path selection in an endpoint. -/
theorem lintegral_translated_path_le {N : ℕ} (G : HomogeneousGroup N)
    {T : Type*} [MeasurableSpace T] (ν : Measure T) [SFinite ν] {S : Set T}
    {B U : Set (Fin N → ℝ)} (hS : MeasurableSet S)
    (γ : T → (Fin N → ℝ)) (F : (Fin N → ℝ) → ℝ≥0∞)
    (hmeas : AEMeasurable (fun p : (Fin N → ℝ) × T => F (G.mul p.1 (γ p.2)))
      ((volume.restrict B).prod (ν.restrict S)))
    (hsub : ∀ t ∈ S, (fun y => G.mul y (γ t)) '' B ⊆ U) :
    (∫⁻ y in B, ∫⁻ t in S, F (G.mul y (γ t)) ∂ν) ≤
      (ν S) * ∫⁻ y in U, F y := by
  rw [lintegral_lintegral_swap hmeas]
  calc
    (∫⁻ t in S, (∫⁻ y in B, F (G.mul y (γ t))) ∂ν) ≤
        ∫⁻ _t in S, (∫⁻ y in U, F y) ∂ν := by
      apply lintegral_mono_ae
      exact ae_restrict_of_forall_mem hS fun t ht =>
        lintegral_rightTranslation_le_of_image_subset G (γ t) (hsub t ht) F
    _ = _ := by simp only [lintegral_const, Measure.restrict_apply_univ, mul_comm]

end HeatKernel
