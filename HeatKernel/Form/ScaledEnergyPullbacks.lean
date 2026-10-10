-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Form.ScaledMeasurePullbacks
public import Mathlib.Analysis.InnerProductSpace.LinearMap
import Mathlib.Tactic.Linter

/-! # Energy pullbacks under smooth homeomorphisms with scaled measure -/

@[expose] public section

noncomputable section

open Set MeasureTheory Filter TopologicalSpace RothschildStein
open scoped ENNReal

namespace HeatKernel

/-- A smooth homeomorphism scaling measure and horizontal derivatives acts on the closed
energy domain with the corresponding bilinear energy scaling. -/
theorem exists_energyGraph_comp_scaledMeasure {N q : ℕ}
    (X : Fin q → (Fin N → ℝ) → (Fin N → ℝ))
    (T : (Fin N → ℝ) ≃ₜ (Fin N → ℝ))
    (hT : ContDiff ℝ (⊤ : ℕ∞) T) {J : ℝ≥0∞} (hJ : J ≠ ⊤)
    (hm : Measure.map T volume = J • volume) (c : ℝ)
    (hD : ∀ f : (Fin N → ℝ) → ℝ, ContDiff ℝ (⊤ : ℕ∞) f → ∀ i,
      fieldDerivative (X i) (f ∘ T) = (fun x => c * fieldDerivative (X i) f (T x)))
    (u v : energyGraph (N := N) ⊤ X) :
    ∃ z w : energyGraph (N := N) ⊤ X,
      ((z : GradientSpace (N := N) ⊤ q).fst =ᵐ[volume] (u : GradientSpace (N := N) ⊤ q).fst ∘ T) ∧
      ((w : GradientSpace (N := N) ⊤ q).fst =ᵐ[volume] (v : GradientSpace (N := N) ⊤ q).fst ∘ T) ∧
      (∀ i, (z : GradientSpace (N := N) ⊤ q).snd i =ᵐ[volume]
        (fun x => c * (u : GradientSpace (N := N) ⊤ q).snd i (T x))) ∧
      (∀ i, (w : GradientSpace (N := N) ⊤ q).snd i =ᵐ[volume]
        (fun x => c * (v : GradientSpace (N := N) ⊤ q).snd i (T x))) ∧
      horizontalEnergy ⊤ X z w = c ^ 2 * J.toReal * horizontalEnergy ⊤ X u v := by
  let μ := volume.restrict ((⊤ : Opens (Fin N → ℝ)) : Set (Fin N → ℝ))
  have hm' : Measure.map T μ = J • μ := by
    simpa only [μ, Opens.coe_top, Measure.restrict_univ] using hm
  have hqm : Measure.QuasiMeasurePreserving T volume volume :=
    ⟨T.continuous.measurable, by rw [hm]; exact Measure.smul_absolutelyContinuous⟩
  let A : SpatialL2 (N := N) ⊤ →L[ℝ] SpatialL2 (N := N) ⊤ :=
    scaledMeasurePullback T.continuous.measurable hm' hJ
  have hAf : ∀ f : SpatialL2 (N := N) ⊤, A f =ᵐ[volume] f ∘ T := by
    intro f
    simpa only [μ, Opens.coe_top, Measure.restrict_univ] using
      scaledMeasurePullback_ae T.continuous.measurable hm' hJ f
  have hAg : ∀ f : SpatialL2 (N := N) ⊤, (c • A f : SpatialL2 (N := N) ⊤) =ᵐ[volume]
      (fun x => c * f (T x)) := by
    intro f
    have H := (Lp.coeFn_smul c (A f)).trans ((scaledMeasurePullback_ae T.continuous.measurable hm' hJ f).fun_comp (c • ·))
    simpa only [μ, Opens.coe_top, Measure.restrict_univ, Pi.smul_def, Function.comp_def, smul_eq_mul] using H
  have hcore : ∀ a ∈ smoothGradientPairs (N := N) (q := q) ⊤ X,
      gradientPullbackPair ⊤ A c a ∈ energyGraph ⊤ X := by
    intro a ha
    obtain ⟨f, hf, hc, _, haf, hag⟩ := ha
    have haf' : a.fst =ᵐ[volume] f := by simpa only [Opens.coe_top, Measure.restrict_univ] using haf
    have hag' : ∀ i, a.snd i =ᵐ[volume] fieldDerivative (X i) f := by
      simpa only [Opens.coe_top, Measure.restrict_univ] using hag
    apply smoothGradientSpan_le_energyGraph ⊤ X
    apply Submodule.subset_span
    refine ⟨f ∘ T, hf.comp hT, hc.comp_homeomorph T, subset_univ _, ?_, fun i => ?_⟩
    · simpa only [gradientPullbackPair, WithLp.toLp_fst, Opens.coe_top, Measure.restrict_univ] using
        (hAf a.fst).trans (hqm.ae_eq_comp haf')
    · have H : (c • A (a.snd i) : SpatialL2 (N := N) ⊤) =ᵐ[volume]
          (fun x => c * fieldDerivative (X i) f (T x)) := by
        filter_upwards [hAg (a.snd i), hqm.ae_eq_comp (hag' i)] with x hx hy
        rw [hx]
        exact congrArg (c * ·) hy
      simpa only [gradientPullbackPair, WithLp.toLp_snd, WithLp.toLp_ofLp, smul_eq_mul,
        Opens.coe_top, Measure.restrict_univ, hD f hf i] using H
  let z : energyGraph (N := N) ⊤ X := ⟨gradientPullbackPair ⊤ A c u,
    gradientPullbackPair_mem_energyGraph ⊤ X A c hcore u⟩
  let w : energyGraph (N := N) ⊤ X := ⟨gradientPullbackPair ⊤ A c v,
    gradientPullbackPair_mem_energyGraph ⊤ X A c hcore v⟩
  refine ⟨z, w, hAf _, hAf _, ?_, ?_, ?_⟩
  · intro i
    simpa only [z, gradientPullbackPair, WithLp.toLp_snd, WithLp.toLp_ofLp, smul_eq_mul] using hAg ((u : GradientSpace (N := N) ⊤ q).snd i)
  · intro i
    simpa only [w, gradientPullbackPair, WithLp.toLp_snd, WithLp.toLp_ofLp, smul_eq_mul] using hAg ((v : GradientSpace (N := N) ⊤ q).snd i)
  · exact horizontalEnergy_pullback_eq ⊤ X A c J.toReal
      (fun f g => inner_scaledMeasurePullback T.measurableEmbedding hm' hJ f g) u v z w rfl rfl


end HeatKernel
