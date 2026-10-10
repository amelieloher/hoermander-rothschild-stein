-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Form.BoundedL2Multipliers
public import HeatKernel.Form.LocalWeakMultipliers
import Mathlib.Tactic.Linter

/-! # Bounded local energy multipliers with bounded horizontal gradients -/

@[expose] public section

noncomputable section

open Set MeasureTheory Filter TopologicalSpace RothschildStein
open scoped Topology

namespace HeatKernel

variable {N q : ℕ}
    {φ : (Fin N → ℝ) → ℝ} {g : Fin q → (Fin N → ℝ) → ℝ} {A B : ℝ}

/-- The function-gradient pair prescribed by the Leibniz rule for a bounded coefficient. -/
def boundedMultiplierPair
    (ha : AEStronglyMeasurable φ (volume.restrict ((⊤ : Opens (Fin N → ℝ)) : Set (Fin N → ℝ))))
    (hg : ∀ i, AEStronglyMeasurable (g i) (volume.restrict ((⊤ : Opens (Fin N → ℝ)) : Set (Fin N → ℝ))))
    (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hb : ∀ᵐ x ∂volume.restrict ((⊤ : Opens (Fin N → ℝ)) : Set (Fin N → ℝ)), ‖φ x‖ ≤ A)
    (hgb : ∀ i, ∀ᵐ x ∂volume.restrict ((⊤ : Opens (Fin N → ℝ)) : Set (Fin N → ℝ)), ‖g i x‖ ≤ B)
    (v : GradientSpace (N := N) ⊤ q) : GradientSpace (N := N) ⊤ q :=
  WithLp.toLp 2 (boundedL2Mul ha hA hb v.fst,
    WithLp.toLp 2 (fun i => boundedL2Mul ha hA hb (v.snd i) + boundedL2Mul (hg i) hB (hgb i) v.fst))

/-- Bounded local energy coefficients with bounded weak gradients multiply the global
horizontal energy domain, with the complete Leibniz formula. -/
theorem exists_energyGraph_mul_bounded_local
    (X : Fin q → (Fin N → ℝ) → (Fin N → ℝ))
    (hX : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (X i)) (u : energyGraph (N := N) ⊤ X)
    (hφ : MemLocalEnergy ⊤ X φ) (hw : ∀ i, hasWeakWordDeriv X ⊤ [i] φ (g i))
    (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hb : ∀ᵐ x ∂volume, ‖φ x‖ ≤ A) (hgb : ∀ i, ∀ᵐ x ∂volume, ‖g i x‖ ≤ B) :
    ∃ z : energyGraph (N := N) ⊤ X,
      (z : GradientSpace (N := N) ⊤ q).fst =ᵐ[volume]
        (fun x => φ x * (u : GradientSpace (N := N) ⊤ q).fst x) ∧
      ∀ i, (z : GradientSpace (N := N) ⊤ q).snd i =ᵐ[volume]
        (fun x => φ x * (u : GradientSpace (N := N) ⊤ q).snd i x +
          g i x * (u : GradientSpace (N := N) ⊤ q).fst x) := by
  let μ := volume.restrict ((⊤ : Opens (Fin N → ℝ)) : Set (Fin N → ℝ))
  have hg' : ∀ i, AEStronglyMeasurable (g i) μ :=
    fun i => (hw i).2.1.aestronglyMeasurable
  have hb' : ∀ᵐ x ∂μ, ‖φ x‖ ≤ A := by
    simpa only [μ, Opens.coe_top, Measure.restrict_univ] using hb
  have hgb' : ∀ i, ∀ᵐ x ∂μ, ‖g i x‖ ≤ B := by
    simpa only [μ, Opens.coe_top, Measure.restrict_univ] using hgb
  let P := boundedMultiplierPair hφ.1 hg' hA hB hb' hgb'
  have hPf : ∀ v : GradientSpace (N := N) ⊤ q,
      (P v).fst =ᵐ[volume] (fun x => φ x * v.fst x) := by
    intro v
    simpa only [P, boundedMultiplierPair, WithLp.toLp_fst, μ, Opens.coe_top, Measure.restrict_univ] using boundedL2Mul_ae hφ.1 hA hb' v.fst
  have hPg : ∀ (v : GradientSpace (N := N) ⊤ q) i,
      (P v).snd i =ᵐ[volume] (fun x => φ x * v.snd i x + g i x * v.fst x) := by
    intro v i
    have H := (Lp.coeFn_add (boundedL2Mul hφ.1 hA hb' (v.snd i))
      (boundedL2Mul (hg' i) hB (hgb' i) v.fst)).trans
      ((boundedL2Mul_ae hφ.1 hA hb' (v.snd i)).add (boundedL2Mul_ae (hg' i) hB (hgb' i) v.fst))
    simpa only [P, boundedMultiplierPair, WithLp.toLp_snd, WithLp.toLp_ofLp, μ, Opens.coe_top, Measure.restrict_univ, Pi.add_def] using H
  obtain ⟨v, hv, ht⟩ := exists_smoothGradientPairs_tendsto ⊤ X u
  have ht' := (tendsto_GradientSpace_iff ⊤).mp ht
  have hm : ∀ n, P (v n) ∈ energyGraph ⊤ X := by
    intro n
    obtain ⟨f, hf, hc, _, hvf, hvg⟩ := hv n
    have hvf' : (v n).fst =ᵐ[volume] f := by
      simpa only [Opens.coe_top, Measure.restrict_univ] using hvf
    have hvg' : ∀ i, (v n).snd i =ᵐ[volume] fieldDerivative (X i) f := by
      simpa only [Opens.coe_top, Measure.restrict_univ] using hvg
    obtain ⟨z, hzf, hzg⟩ := hφ.exists_mul_smooth_compact_of_weakGradient X hX hw hf hc
    have he : P (v n) = (z : GradientSpace (N := N) ⊤ q) := by
      apply (WithLp.ext_iff 2).mpr
      apply Prod.ext
      · apply Lp.ext
        have H : (P (v n)).fst =ᵐ[volume] (z : GradientSpace (N := N) ⊤ q).fst := by
          filter_upwards [hPf (v n), hvf', hzf] with x hx hxf hzx
          rw [hx, hxf, hzx]
        simpa only [WithLp.fst, Opens.coe_top, Measure.restrict_univ] using H
      · apply PiLp.ext
        intro i
        apply Lp.ext
        have H : (P (v n)).snd i =ᵐ[volume] (z : GradientSpace (N := N) ⊤ q).snd i := by
          filter_upwards [hPg (v n) i, hvg' i, hvf', hzg i] with x hx hxg hxf hzx
          rw [hx, hxg, hxf, hzx]
        simpa only [WithLp.snd, Opens.coe_top, Measure.restrict_univ] using H
    exact he.symm ▸ z.property
  have hPm : P (u : GradientSpace (N := N) ⊤ q) ∈ energyGraph ⊤ X := by
    apply mem_energyGraph_of_componentwise_tendsto ⊤ X hm
    · exact tendsto_boundedL2Mul hφ.1 hA hb' ht'.1
    · intro i
      exact (tendsto_boundedL2Mul hφ.1 hA hb' (ht'.2 i)).add
        (tendsto_boundedL2Mul (hg' i) hB (hgb' i) ht'.1)
  exact ⟨⟨P (u : GradientSpace (N := N) ⊤ q), hPm⟩, hPf _, hPg _⟩



end HeatKernel
