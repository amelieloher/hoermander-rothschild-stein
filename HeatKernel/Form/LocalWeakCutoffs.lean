-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Form.CompactGradientApproximation
public import HeatKernel.Form.ScalarComposition
public import RothschildStein.S.Leibniz
public import RothschildStein.S.ZeroExtension
import Mathlib.Tactic.Linter

/-! # Interior cutoffs of local weak horizontal gradients -/

@[expose] public section

noncomputable section

open Set MeasureTheory Filter TopologicalSpace RothschildStein
open scoped ENNReal

namespace HeatKernel

/-- A function vanishing off an open set has the same global Lp membership as its restriction. -/
theorem memLp_global_of_restrict_of_zero_outside {N : ℕ} (U : Opens (Fin N → ℝ))
    {f : (Fin N → ℝ) → ℝ} {p : ℝ≥0∞}
    (hf : MemLp f p (volume.restrict (U : Set (Fin N → ℝ))))
    (hz : ∀ x ∉ (U : Set (Fin N → ℝ)), f x = 0) : MemLp f p volume := by
  have he : (U : Set (Fin N → ℝ)).indicator f = f := by
    funext x
    by_cases hx : x ∈ (U : Set (Fin N → ℝ))
    · exact indicator_of_mem hx f
    · rw [indicator_of_notMem hx, hz x hx]
  exact he ▸ (S.memLp_zeroExtension_iff U.isOpen.measurableSet f).mpr hf

/-- A smooth interior cutoff of square-integrable local weak-gradient data has a global energy
representative with the full Leibniz gradient. -/
theorem exists_energyGraph_mul_of_local_weakGradient {N q : ℕ}
    (U : Opens (Fin N → ℝ)) (X : Fin q → (Fin N → ℝ) → (Fin N → ℝ))
    (hX : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (X i))
    (f : (Fin N → ℝ) → ℝ) (g : Fin q → (Fin N → ℝ) → ℝ)
    (hf : MemLp f 2 (volume.restrict (U : Set (Fin N → ℝ))))
    (hg : ∀ i, MemLp (g i) 2 (volume.restrict (U : Set (Fin N → ℝ))))
    (hw : ∀ i, hasWeakWordDeriv X U [i] f (g i))
    {φ : (Fin N → ℝ) → ℝ} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hc : HasCompactSupport φ) (hs : tsupport φ ⊆ (U : Set (Fin N → ℝ))) :
    ∃ z : energyGraph (N := N) ⊤ X,
      (z : GradientSpace (N := N) ⊤ q).fst =ᵐ[volume] (fun x => f x * φ x) ∧
      ∀ i, (z : GradientSpace (N := N) ⊤ q).snd i =ᵐ[volume]
        (fun x => g i x * φ x + f x * fieldDerivative (X i) φ x) := by
  have hD : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (fieldDerivative (X i) φ) := fun i => by
    simpa only [Opens.coe_top, contDiffOn_univ] using
      S.contDiffOn_fieldDerivative ⊤ (X i) φ (hX i).contDiffOn hφ.contDiffOn
  have hcD : ∀ i, HasCompactSupport (fieldDerivative (X i) φ) := fun i =>
    hc.of_isClosed_subset (isClosed_tsupport _) (S.tsupport_fieldDerivative_subset (X i) φ)
  obtain ⟨A, hA⟩ := hc.exists_bound_of_continuous hφ.continuous
  choose B hB using fun i => (hcD i).exists_bound_of_continuous (hD i).continuous
  have hAp : 0 ≤ A := (norm_nonneg _).trans (hA 0)
  have hBp : ∀ i, 0 ≤ B i := fun i => (norm_nonneg _).trans (hB i 0)
  have hzero : ∀ x ∉ (U : Set (Fin N → ℝ)), φ x = 0 := fun x hx =>
    image_eq_zero_of_notMem_tsupport (fun ht => hx (hs ht))
  have hDzero : ∀ i x, x ∉ (U : Set (Fin N → ℝ)) → fieldDerivative (X i) φ x = 0 :=
    fun i x hx => image_eq_zero_of_notMem_tsupport
      (fun ht => hx (hs (S.tsupport_fieldDerivative_subset (X i) φ ht)))
  have hfp : MemLp (fun x => f x * φ x) 2 volume := by
    apply memLp_global_of_restrict_of_zero_outside U
    · simpa only [mul_comm] using memLp_mul_of_ae_bound hφ.continuous.aestronglyMeasurable
        hf hAp (Eventually.of_forall hA)
    · intro x hx
      rw [hzero x hx, mul_zero]
  have hgp : ∀ i, MemLp (fun x => g i x * φ x + f x * fieldDerivative (X i) φ x) 2 volume := by
    intro i
    apply memLp_global_of_restrict_of_zero_outside U
    · have H₁ := memLp_mul_of_ae_bound hφ.continuous.aestronglyMeasurable
        (hg i) hAp (Eventually.of_forall hA)
      have H₂ := memLp_mul_of_ae_bound (hD i).continuous.aestronglyMeasurable
        hf (hBp i) (Eventually.of_forall (hB i))
      simpa only [Pi.add_def, mul_comm] using H₁.add H₂
    · intro x hx
      rw [hzero x hx, hDzero i x hx, mul_zero, mul_zero, zero_add]
  have hwglobal : ∀ i, hasWeakWordDeriv X ⊤ [i] (fun x => f x * φ x)
      (fun x => g i x * φ x + f x * fieldDerivative (X i) φ x) := by
    intro i
    have H := S.hasWeakWordDeriv_zeroExtension X ⊤ U (subset_univ _)
      ⟨tsupport φ, hc⟩ hs [i] _ _
      (S.hasWeakWordDeriv_mul_one X U (fun j => (hX j).contDiffOn) i f (g i) φ hφ.contDiffOn (hw i))
      (Eventually.of_forall fun x _ hx => by rw [image_eq_zero_of_notMem_tsupport hx, mul_zero])
    have he₁ : (U : Set (Fin N → ℝ)).indicator (fun x => f x * φ x) = (fun x => f x * φ x) := by
      funext x
      by_cases hx : x ∈ (U : Set (Fin N → ℝ))
      · exact indicator_of_mem hx _
      · rw [indicator_of_notMem hx, hzero x hx, mul_zero]
    have he₂ : (U : Set (Fin N → ℝ)).indicator
        (fun x => g i x * φ x + f x * fieldDerivative (X i) φ x) =
        (fun x => g i x * φ x + f x * fieldDerivative (X i) φ x) := by
      funext x
      by_cases hx : x ∈ (U : Set (Fin N → ℝ))
      · exact indicator_of_mem hx _
      · rw [indicator_of_notMem hx, hzero x hx, hDzero i x hx, mul_zero, mul_zero, zero_add]
    rwa [he₁, he₂] at H
  have hfp' : MemLp (fun x => f x * φ x) 2
      (volume.restrict ((⊤ : Opens (Fin N → ℝ)) : Set (Fin N → ℝ))) := by
    simpa only [Opens.coe_top, Measure.restrict_univ] using hfp
  have hgp' : ∀ i, MemLp (fun x => g i x * φ x + f x * fieldDerivative (X i) φ x) 2
      (volume.restrict ((⊤ : Opens (Fin N → ℝ)) : Set (Fin N → ℝ))) := by
    simpa only [Opens.coe_top, Measure.restrict_univ] using hgp
  let z : GradientSpace (N := N) ⊤ q := WithLp.toLp 2
    (hfp'.toLp _, WithLp.toLp 2 (fun i => (hgp' i).toLp _))
  have hzf : z.fst =ᵐ[volume] (fun x => f x * φ x) := by
    simpa only [z, WithLp.toLp_fst, Opens.coe_top, Measure.restrict_univ] using hfp'.coeFn_toLp
  have hzg : ∀ i, z.snd i =ᵐ[volume]
      (fun x => g i x * φ x + f x * fieldDerivative (X i) φ x) := by
    intro i
    simpa only [z, WithLp.toLp_snd, WithLp.toLp_ofLp, Opens.coe_top, Measure.restrict_univ] using (hgp' i).coeFn_toLp
  have hzw : z ∈ weakGradientGraph ⊤ X (fun i => (hX i).contDiffOn) := by
    intro i
    apply S.hasWeakWordDeriv_congr_ae X ⊤ (hwglobal i)
    · simpa only [Opens.coe_top, Measure.restrict_univ] using hzf.symm
    · simpa only [Opens.coe_top, Measure.restrict_univ] using (hzg i).symm
  have hm := mem_energyGraph_of_compact_weakGradient X hX ⟨z, hzw⟩
    (f := fun x => f x * φ x) hc.mul_left hzf
  exact ⟨⟨z, hm⟩, hzf, hzg⟩


end HeatKernel
