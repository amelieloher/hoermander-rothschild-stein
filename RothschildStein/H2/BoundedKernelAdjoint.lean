-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H2.IntegralDefs
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set MeasureTheory Metric
open scoped ENNReal

namespace RothschildStein.H2
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]

omit [MetricSpace X] [BorelSpace X] in
/-- Fubini for a bounded measurable kernel on a finite patch.
This is applied to each positive truncation, before passing to a PV limit. -/
theorem bounded_kernel_adjoint {μ : Measure X} {U : Set X} (hU : MeasurableSet U)
    (hμ : μ U < ⊤) {K : X → X → ℝ}
    (hK : Measurable (fun p : U × U => K p.1 p.2))
    {M : ℝ} (hM : 0 ≤ M) (hbound : ∀ x ∈ U, ∀ y ∈ U, |K x y| ≤ M)
    {f g : X → ℝ} (hf : Measurable (fun x : U => f x))
    (hg : Measurable (fun x : U => g x)) {F G : ℝ} (hF : 0 ≤ F) (_hG : 0 ≤ G)
    (hfb : ∀ x ∈ U, |f x| ≤ F) (hgb : ∀ x ∈ U, |g x| ≤ G) :
    (∫ x in U, (∫ y in U, K x y * f y ∂μ) * g x ∂μ) =
      ∫ y in U, f y * (∫ x in U, K x y * g x ∂μ) ∂μ := by
  let ν : Measure U := μ.comap Subtype.val
  have hν : ν univ < ⊤ := by
    change (μ.comap Subtype.val) univ < ⊤
    rw [(MeasurableEmbedding.subtype_coe hU).comap_apply μ univ]
    simpa only [image_univ, Subtype.range_coe] using hμ
  let : IsFiniteMeasure ν := ⟨hν⟩
  let H : U → U → ℝ := fun x y => K x y * f y * g x
  have hm : Measurable (Function.uncurry H) := (hK.mul (hf.comp measurable_snd)).mul (hg.comp measurable_fst)
  have hb : ∀ p : U × U, ‖Function.uncurry H p‖ ≤ M * F * G := by
    intro p
    change |K p.1 p.2 * f p.2 * g p.1| ≤ _
    rw [abs_mul, abs_mul]
    exact mul_le_mul (mul_le_mul (hbound _ p.1.property _ p.2.property)
      (hfb _ p.2.property) (abs_nonneg _) hM) (hgb _ p.1.property)
      (abs_nonneg _) (mul_nonneg hM hF)
  have hi : Integrable (Function.uncurry H) (ν.prod ν) :=
    memLp_one_iff_integrable.mp (MemLp.of_bound hm.aestronglyMeasurable (M * F * G) (ae_of_all _ hb))
  have he := integral_integral_swap hi
  have hl : (∫ x : U, ∫ y : U, H x y ∂ν ∂ν) =
      ∫ x in U, (∫ y in U, K x y * f y ∂μ) * g x ∂μ := by
    calc
      _ = ∫ x : U, (∫ y in U, K x y * f y ∂μ) * g x ∂ν := by
        apply integral_congr_ae
        exact ae_of_all _ fun x => by
          change (∫ y : U, K x y * f y * g x ∂ν) = _
          rw [integral_mul_const]
          change (∫ y : U, K x y * f y ∂μ.comap Subtype.val) * g x = _
          rw [integral_subtype_comap hU (fun y => K x y * f y)]
      _ = _ := integral_subtype_comap (μ := μ) hU (fun x => (∫ y in U, K x y * f y ∂μ) * g x)
  have hr : (∫ y : U, ∫ x : U, H x y ∂ν ∂ν) =
      ∫ y in U, f y * (∫ x in U, K x y * g x ∂μ) ∂μ := by
    calc
      _ = ∫ y : U, f y * (∫ x in U, K x y * g x ∂μ) ∂ν := by
        apply integral_congr_ae
        exact ae_of_all _ fun y => by
          change (∫ x : U, K x y * f y * g x ∂ν) = _
          have hh : (fun x : U => K x y * f y * g x) =
              (fun x : U => f y * (K x y * g x)) := by funext x; ring
          rw [hh, integral_const_mul]
          change f y * (∫ x : U, K x y * g x ∂μ.comap Subtype.val) = _
          rw [integral_subtype_comap hU (fun x => K x y * g x)]
      _ = _ := integral_subtype_comap (μ := μ) hU (fun y => f y * (∫ x in U, K x y * g x ∂μ))
  exact hl.symm.trans (he.trans hr)

end RothschildStein.H2
