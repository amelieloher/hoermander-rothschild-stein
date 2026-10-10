-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Bridge.AlmostEverywhereSupportedPairings
public import HeatKernel.Bridge.TimeIntegratedFormTests
public import HeatKernel.Sobolev.ZeroBoundarySupport
public import HeatKernel.Sobolev.ZeroBoundaryGradientSupport
import Mathlib.Tactic.Linter

/-! # Literal integrable pairings with zero-boundary horizontal form tests -/

@[expose] public section
open Set MeasureTheory TopologicalSpace
namespace HeatKernel

/-- Localized L² data paired with a zero-boundary form test give separately
integrable literal value and flux terms and their concrete integral formula. -/
theorem localized_form_test_pairings {α : Type*} [MeasurableSpace α]
    (μ : Measure α) [IsFiniteMeasure μ] {N q : ℕ}
    (V : Opens (Fin N → ℝ)) (X : Fin q → (Fin N → ℝ) → (Fin N → ℝ))
    {K : Set (Fin N → ℝ)} (hVK : (V : Set (Fin N → ℝ)) ⊆ K)
    (f : α × (Fin N → ℝ) → ℝ) (h : Fin q → α × (Fin N → ℝ) → ℝ)
    (T : Lp ℝ 2 (μ.prod (volume.restrict ((⊤ : Opens (Fin N → ℝ)) : Set (Fin N → ℝ)))))
    (F : Fin q → Lp ℝ 2 (μ.prod (volume.restrict ((⊤ : Opens (Fin N → ℝ)) : Set (Fin N → ℝ)))))
    (hT : (T : α × (Fin N → ℝ) → ℝ) =ᵐ[μ.prod volume]
      (fun z => K.indicator (fun x => f (z.1, x)) z.2))
    (hF : ∀ i, (F i : α × (Fin N → ℝ) → ℝ) =ᵐ[μ.prod volume]
      (fun z => K.indicator (fun x => h i (z.1, x)) z.2))
    (v : zeroBoundaryGraph V X) :
    Integrable (fun z => f z * (v : GradientSpace (N := N) ⊤ q).fst z.2) (μ.prod volume) ∧
    (∀ i, Integrable (fun z => h i z * (v : GradientSpace (N := N) ⊤ q).snd i z.2)
      (μ.prod volume)) ∧
    timeIntegratedFormTest μ X T F ⟨v, zeroBoundaryGraph_le_energyGraph V X v.property⟩ =
      (∫ z, f z * (v : GradientSpace (N := N) ⊤ q).fst z.2 ∂μ.prod volume) +
        ∑ i, ∫ z, h i z * (v : GradientSpace (N := N) ⊤ q).snd i z.2 ∂μ.prod volume := by
  have hz : ∀ᵐ x ∂volume, x ∉ K → (v : GradientSpace (N := N) ⊤ q).fst x = 0 :=
    (Sobolev.ae_eq_zero_outside_of_mem_zeroBoundaryGraph V X v).mono
      (fun _ hx hn => hx (fun h => hn (hVK h)))
  have hzg (i : Fin q) : ∀ᵐ x ∂volume, x ∉ K →
      (v : GradientSpace (N := N) ⊤ q).snd i x = 0 :=
    (Sobolev.ae_eq_zero_gradient_outside_of_mem_zeroBoundaryGraph V X v i).mono
      (fun _ hx hn => hx (fun h => hn (hVK h)))
  have ht := ae_mul_eq_of_ae_spatial_indicator_of_ae_zero (f := f) hT hz
  have hf (i : Fin q) := ae_mul_eq_of_ae_spatial_indicator_of_ae_zero (f := h i) (hF i) (hzg i)
  have htLp : MemLp (T : α × (Fin N → ℝ) → ℝ) 2 (μ.prod volume) := by
    simpa only [Opens.coe_top, Measure.restrict_univ] using Lp.memLp T
  have hfLp (i : Fin q) : MemLp (F i : α × (Fin N → ℝ) → ℝ) 2 (μ.prod volume) := by
    simpa only [Opens.coe_top, Measure.restrict_univ] using Lp.memLp (F i)
  have hvLp : MemLp ((v : GradientSpace (N := N) ⊤ q).fst : (Fin N → ℝ) → ℝ) 2 volume := by
    simpa only [Opens.coe_top, Measure.restrict_univ] using
      Lp.memLp (v : GradientSpace (N := N) ⊤ q).fst
  have hgLp (i : Fin q) : MemLp ((v : GradientSpace (N := N) ⊤ q).snd i : (Fin N → ℝ) → ℝ) 2 volume := by
    simpa only [Opens.coe_top, Measure.restrict_univ] using
      Lp.memLp ((v : GradientSpace (N := N) ⊤ q).snd i)
  refine ⟨(htLp.integrable_mul (hvLp.comp_snd μ)).congr ht,
    fun i => ((hfLp i).integrable_mul ((hgLp i).comp_snd μ)).congr (hf i), ?_⟩
  rw [timeIntegratedFormTest_apply, integral_congr_ae ht]
  exact congrArg (fun r => (∫ z, f z * (v : GradientSpace (N := N) ⊤ q).fst z.2 ∂μ.prod volume) + r)
    (Finset.sum_congr rfl (fun i _ => integral_congr_ae (hf i)))

end HeatKernel
