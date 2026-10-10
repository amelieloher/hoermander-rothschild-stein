-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Form.CutoffProductL2
public import HeatKernel.Form.EnergyCurveSelection
public import HeatKernel.Form.BochnerFlux
import Mathlib.Tactic.Linter

/-! # Bochner energy curves from local weak-gradient data -/

@[expose] public section

noncomputable section

open Set MeasureTheory Filter TopologicalSpace RothschildStein

namespace HeatKernel

/-- Joint L² local weak-gradient data become a Bochner L² curve in the global horizontal graph
after multiplication by a smooth interior spatial cutoff. -/
theorem exists_cutoff_energyGraph_curve {α : Type*} [MeasurableSpace α]
    {μ : Measure α} [SFinite μ] {N q : ℕ} (U : Opens (Fin N → ℝ))
    (X : Fin q → (Fin N → ℝ) → (Fin N → ℝ))
    (hX : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (X i))
    (u : α → (Fin N → ℝ) → ℝ) (g : Fin q → α → (Fin N → ℝ) → ℝ)
    (hu : MemLp (Function.uncurry u) 2 (μ.prod (volume.restrict (U : Set (Fin N → ℝ)))))
    (hg : ∀ i, MemLp (Function.uncurry (g i)) 2 (μ.prod (volume.restrict (U : Set (Fin N → ℝ)))))
    (hw : ∀ᵐ t ∂μ, ∀ i, hasWeakWordDeriv X U [i] (u t) (g i t))
    {φ : (Fin N → ℝ) → ℝ} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hc : HasCompactSupport φ)
    (hs : tsupport φ ⊆ (U : Set (Fin N → ℝ))) :
    ∃ v : α → energyGraph (N := N) ⊤ X, MemLp v 2 μ ∧
      (∀ᵐ t ∂μ, (v t : GradientSpace (N := N) ⊤ q).fst =ᵐ[volume] fun x => u t x * φ x) ∧
      ∀ i, ∀ᵐ t ∂μ, (v t : GradientSpace (N := N) ⊤ q).snd i =ᵐ[volume]
        fun x => g i t x * φ x + u t x * fieldDerivative (X i) φ x := by
  have hD : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (fieldDerivative (X i) φ) := fun i => by
    simpa only [Opens.coe_top, contDiffOn_univ] using
      S.contDiffOn_fieldDerivative ⊤ (X i) φ (hX i).contDiffOn hφ.contDiffOn
  have hcD : ∀ i, HasCompactSupport (fieldDerivative (X i) φ) := fun i =>
    hc.of_isClosed_subset (isClosed_tsupport _) (S.tsupport_fieldDerivative_subset (X i) φ)
  have hsD : ∀ i, tsupport (fieldDerivative (X i) φ) ⊆ (U : Set (Fin N → ℝ)) :=
    fun i => (S.tsupport_fieldDerivative_subset (X i) φ).trans hs
  have huf := memLp_product_mul_smooth_compact U hu hφ hc hs
  have hgf : ∀ i, MemLp (fun z : α × (Fin N → ℝ) =>
      g i z.1 z.2 * φ z.2 + u z.1 z.2 * fieldDerivative (X i) φ z.2) 2 (μ.prod volume) := by
    intro i
    simpa only [Pi.add_def] using
      (memLp_product_mul_smooth_compact U (hg i) hφ hc hs).add
        (memLp_product_mul_smooth_compact U hu (hD i) (hcD i) (hsD i))
  have hex : ∀ᵐ t ∂μ, ∃ w : energyGraph (N := N) ⊤ X,
      (w : GradientSpace (N := N) ⊤ q).fst =ᵐ[volume]
        (fun x => u t x * φ x) ∧
      ∀ i, (w : GradientSpace (N := N) ⊤ q).snd i =ᵐ[volume]
        (fun x => g i t x * φ x + u t x * fieldDerivative (X i) φ x) := by
    filter_upwards [ae_memLp_slice_of_product_memLp hu,
      ae_all_iff.mpr (fun i => ae_memLp_slice_of_product_memLp (hg i)), hw] with t ht hgt hwt
    exact exists_energyGraph_mul_of_local_weakGradient U X hX (u t) (fun i => g i t)
      ht hgt hwt hφ hc hs
  have hu' : MemLp (Function.uncurry (fun t x => u t x * φ x)) 2
      (μ.prod (volume.restrict ((⊤ : Opens (Fin N → ℝ)) : Set (Fin N → ℝ)))) := by
    simpa only [Opens.coe_top, Measure.restrict_univ, Function.uncurry_def] using huf
  have hg' : ∀ i, MemLp (Function.uncurry
      (fun t x => g i t x * φ x + u t x * fieldDerivative (X i) φ x)) 2
      (μ.prod (volume.restrict ((⊤ : Opens (Fin N → ℝ)) : Set (Fin N → ℝ)))) := by
    simpa only [Opens.coe_top, Measure.restrict_univ, Function.uncurry_def] using hgf
  have hex' : ∀ᵐ t ∂μ, ∃ w : energyGraph (N := N) ⊤ X,
      (w : GradientSpace (N := N) ⊤ q).fst =ᵐ[volume.restrict
        ((⊤ : Opens (Fin N → ℝ)) : Set (Fin N → ℝ))] (fun x => u t x * φ x) ∧
      ∀ i, (w : GradientSpace (N := N) ⊤ q).snd i =ᵐ[volume.restrict
        ((⊤ : Opens (Fin N → ℝ)) : Set (Fin N → ℝ))]
        (fun x => g i t x * φ x + u t x * fieldDerivative (X i) φ x) := by
    simpa only [Opens.coe_top, Measure.restrict_univ] using hex
  obtain ⟨v, hv⟩ := exists_energyGraph_curve_of_ae_representatives ⊤ X
    (fun t x => u t x * φ x) (fun i t x => g i t x * φ x + u t x * fieldDerivative (X i) φ x)
    hu' hg' hex'
  exact ⟨v, by simpa only [Opens.coe_top, Measure.restrict_univ] using hv⟩



end HeatKernel
