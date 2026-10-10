-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Form.CompactGradientApproximation
public import HeatKernel.Form.ScalarComposition
public import RothschildStein.S.Leibniz

/-! # Smooth compact multipliers on the horizontal energy domain -/

@[expose] public section

noncomputable section

open Set MeasureTheory TopologicalSpace RothschildStein

namespace HeatKernel

/-- Multiplication by a smooth compact function preserves the global energy domain,
including the horizontal Leibniz formula. -/
theorem exists_energyGraph_mul_smooth_compact {N q : ℕ}
    (X : Fin q → (Fin N → ℝ) → (Fin N → ℝ))
    (hX : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (X i))
    (u : energyGraph (N := N) ⊤ X) {φ : (Fin N → ℝ) → ℝ}
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hc : HasCompactSupport φ) :
    ∃ z : energyGraph (N := N) ⊤ X,
      (z : GradientSpace (N := N) ⊤ q).fst =ᵐ[volume]
        (fun x => (u : GradientSpace (N := N) ⊤ q).fst x * φ x) ∧
      ∀ i, (z : GradientSpace (N := N) ⊤ q).snd i =ᵐ[volume]
        (fun x => (u : GradientSpace (N := N) ⊤ q).snd i x * φ x +
          (u : GradientSpace (N := N) ⊤ q).fst x * fieldDerivative (X i) φ x) := by
  let U : Opens (Fin N → ℝ) := ⊤
  let μ := volume.restrict (U : Set (Fin N → ℝ))
  have hD : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (fieldDerivative (X i) φ) := fun i => by
    simpa only [U, Opens.coe_top, contDiffOn_univ] using
      S.contDiffOn_fieldDerivative U (X i) φ (hX i).contDiffOn hφ.contDiffOn
  have hcD : ∀ i, HasCompactSupport (fieldDerivative (X i) φ) := fun i =>
    hc.of_isClosed_subset (isClosed_tsupport _) (S.tsupport_fieldDerivative_subset (X i) φ)
  obtain ⟨A, hA⟩ := hc.exists_bound_of_continuous hφ.continuous
  have hAp : 0 ≤ A := (norm_nonneg _).trans (hA 0)
  choose B hB using fun i => (hcD i).exists_bound_of_continuous (hD i).continuous
  have hBp : ∀ i, 0 ≤ B i := fun i => (norm_nonneg _).trans (hB i 0)
  have hm : ∀ (f : SpatialL2 U), MemLp (fun x => f x * φ x) 2 μ := fun f => by
    simpa only [mul_comm] using memLp_mul_of_ae_bound hφ.continuous.aestronglyMeasurable
      (Lp.memLp f) hAp (Filter.Eventually.of_forall hA)
  have hmD : ∀ i, MemLp (fun x => (u : GradientSpace U q).fst x * fieldDerivative (X i) φ x) 2 μ :=
    fun i => by
      simpa only [mul_comm] using memLp_mul_of_ae_bound (hD i).continuous.aestronglyMeasurable
        (Lp.memLp (u : GradientSpace U q).fst) (hBp i) (Filter.Eventually.of_forall (hB i))
  have hmg : ∀ i, MemLp (fun x => (u : GradientSpace U q).snd i x * φ x +
      (u : GradientSpace U q).fst x * fieldDerivative (X i) φ x) 2 μ :=
    fun i => (hm ((u : GradientSpace U q).snd i)).add (hmD i)
  let z : GradientSpace U q := WithLp.toLp 2
    ((hm (u : GradientSpace U q).fst).toLp (fun x => (u : GradientSpace U q).fst x * φ x),
      WithLp.toLp 2 (fun i => (hmg i).toLp (fun x =>
        (u : GradientSpace U q).snd i x * φ x +
          (u : GradientSpace U q).fst x * fieldDerivative (X i) φ x)))
  have hzf : z.fst =ᵐ[μ] fun x => (u : GradientSpace U q).fst x * φ x :=
    (hm (u : GradientSpace U q).fst).coeFn_toLp
  have hzg : ∀ i, z.snd i =ᵐ[μ] fun x => (u : GradientSpace U q).snd i x * φ x +
      (u : GradientSpace U q).fst x * fieldDerivative (X i) φ x := fun i => (hmg i).coeFn_toLp
  have hw := energyGraph_le_weakGradientGraph U X (fun i => (hX i).contDiffOn) u.property
  have hzweak : z ∈ weakGradientGraph U X (fun i => (hX i).contDiffOn) := by
    intro i
    exact S.hasWeakWordDeriv_congr_ae X U
      (S.hasWeakWordDeriv_mul_one X U (fun j => (hX j).contDiffOn) i
        (u : GradientSpace U q).fst ((u : GradientSpace U q).snd i) φ hφ.contDiffOn (hw i))
      hzf.symm (hzg i).symm
  have hmem : z ∈ energyGraph U X :=
    mem_energyGraph_of_compact_weakGradient X hX ⟨z, hzweak⟩ (f := fun x => (u : GradientSpace U q).fst x * φ x) hc.mul_left
      (by simpa only [μ, U, Opens.coe_top, Measure.restrict_univ, Pi.mul_apply] using hzf)
  refine ⟨⟨z, hmem⟩, ?_, fun i => ?_⟩
  · simpa only [μ, U, Opens.coe_top, Measure.restrict_univ] using hzf
  · simpa only [μ, U, Opens.coe_top, Measure.restrict_univ] using hzg i

end HeatKernel
