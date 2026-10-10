-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import Mathlib
public import HeatKernel.Moser.StationaryWeakIdentity
public import HeatKernel.Moser.StationaryEnergy

/-!
# Time sections of smooth space-time tests

Smooth compactly supported space-time tests have smooth compactly supported time
sections. Their temporal differential therefore has zero integral against a
stationary multiplier whenever the product is integrable.
-/

@[expose] public section

open Set MeasureTheory Topology

namespace HeatKernel

/-- Restricting a compactly supported function to a fixed spatial point preserves compact support. -/
theorem hasCompactSupport_timeSection {E : Type*} [TopologicalSpace E] [T1Space E]
    {φ : ℝ × E → ℝ} (hc : HasCompactSupport φ) (x : E) :
    HasCompactSupport (fun t => φ (t, x)) := by
  have he : IsClosedEmbedding (fun t : ℝ => (t, x)) := by
    refine ⟨isEmbedding_prodMkLeft x, ?_⟩
    have hr : Set.range (fun t : ℝ => (t, x)) = Prod.snd ⁻¹' {x} := by
      ext z
      simp only [Set.mem_range, Set.mem_preimage, Set.mem_singleton_iff]
      constructor
      · rintro ⟨t, rfl⟩
        rfl
      · intro hz
        exact ⟨z.1, Prod.ext rfl hz.symm⟩
    rw [hr]
    exact isClosed_singleton.preimage continuous_snd
  exact hc.comp_isClosedEmbedding he

/-- The derivative of a time section is the space-time differential in the time direction. -/
theorem deriv_timeSection_eq_fderiv {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {φ : ℝ × E → ℝ} (hφ : Differentiable ℝ φ) (t : ℝ) (x : E) :
    deriv (fun s => φ (s, x)) t = fderiv ℝ φ (t, x) (1, 0) := by
  have h := (hφ (t, x)).hasFDerivAt.comp t (hasFDerivAt_prodMk_left (𝕜 := ℝ) t x)
  simpa [Function.comp_def] using h.hasDerivAt.deriv

/-- The temporal differential of a smooth compact space-time test annihilates stationary multipliers. -/
theorem integral_stationary_mul_fderiv_time_eq_zero_of_integrable
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasurableSpace E] {μ : Measure E} [SFinite μ]
    {u : E → ℝ} {φ : ℝ × E → ℝ}
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hc : HasCompactSupport φ)
    (hi : Integrable (fun z : ℝ × E => u z.2 * fderiv ℝ φ z (1, 0))
      (volume.prod μ)) :
    (∫ z : ℝ × E, u z.2 * fderiv ℝ φ z (1, 0) ∂volume.prod μ) = 0 := by
  have hd := hφ.differentiable (by simp)
  have he : (fun z : ℝ × E => u z.2 * fderiv ℝ φ z (1, 0)) =
      (fun z : ℝ × E => u z.2 * deriv (fun t => φ (t, z.2)) z.1) := by
    funext z
    rw [deriv_timeSection_eq_fderiv hd]
  rw [he] at hi ⊢
  apply integral_stationary_mul_timeDeriv_eq_zero_of_integrable
      (φ := fun t x => φ (t, x)) _ (hasCompactSupport_timeSection hc) hi
  intro x
  exact (hφ.comp (contDiff_id.prodMk contDiff_const)).of_le (by simp)

/-- Local horizontal Sobolev membership makes the stationary temporal test term integrable. -/
theorem integrable_stationary_mul_fderiv_time {m n : ℕ}
    {X : Fin m → (Fin n → ℝ) → (Fin n → ℝ)}
    {Ω : TopologicalSpace.Opens (Fin n → ℝ)} {u : (Fin n → ℝ) → ℝ}
    (hu : RothschildStein.memSobolevXLoc RothschildStein.noDriftWeight X Ω 1 2 u)
    {φ : ℝ × (Fin n → ℝ) → ℝ} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hc : HasCompactSupport φ) (hs : tsupport φ ⊆ Prod.snd ⁻¹' (Ω : Set (Fin n → ℝ))) :
    Integrable (fun z : ℝ × (Fin n → ℝ) => u z.2 * fderiv ℝ φ z (1, 0)) := by
  let J := Prod.fst '' tsupport φ
  let K := Prod.snd '' tsupport φ
  have hJ : IsCompact J := hc.image continuous_fst
  have hK : IsCompact K := hc.image continuous_snd
  have hKU : K ⊆ (Ω : Set (Fin n → ℝ)) := by
    rintro x ⟨z, hz, rfl⟩
    exact hs hz
  have huLp := memLp_two_stationary_on_compact_time
    (memLp_two_on_compact_of_memSobolevXLoc hu hK hKU) hJ
  have hd : Continuous (fun z => fderiv ℝ φ z (1, 0)) :=
    (hφ.continuous_fderiv (by simp)).clm_apply continuous_const
  have hdLp : MemLp (fun z => fderiv ℝ φ z (1, 0)) 2
      (volume : Measure (ℝ × (Fin n → ℝ))) :=
    hd.memLp_of_hasCompactSupport (hc.fderiv_apply ℝ (1, 0))
  have hi := huLp.integrable_mul (hdLp.restrict (J ×ˢ K))
  apply (integrableOn_iff_integrable_of_support_subset (s := J ×ˢ K) ?_).mp hi
  intro z hz
  have hdz : fderiv ℝ φ z (1, 0) ≠ 0 := (mul_ne_zero_iff.mp hz).2
  have hzφ : z ∈ tsupport φ :=
    tsupport_fderiv_apply_subset ℝ (1, 0) (subset_tsupport _ hdz)
  exact ⟨⟨z, hzφ, rfl⟩, ⟨z, hzφ, rfl⟩⟩

/-- A stationary local horizontal Sobolev function annihilates every compact temporal test term. -/
theorem integral_stationary_mul_fderiv_time_eq_zero {m n : ℕ}
    {X : Fin m → (Fin n → ℝ) → (Fin n → ℝ)}
    {Ω : TopologicalSpace.Opens (Fin n → ℝ)} {u : (Fin n → ℝ) → ℝ}
    (hu : RothschildStein.memSobolevXLoc RothschildStein.noDriftWeight X Ω 1 2 u)
    {φ : ℝ × (Fin n → ℝ) → ℝ} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hc : HasCompactSupport φ) (hs : tsupport φ ⊆ Prod.snd ⁻¹' (Ω : Set (Fin n → ℝ))) :
    (∫ z : ℝ × (Fin n → ℝ), u z.2 * fderiv ℝ φ z (1, 0)) = 0 := by
  exact integral_stationary_mul_fderiv_time_eq_zero_of_integrable hφ hc
    (integrable_stationary_mul_fderiv_time hu hφ hc hs)

end HeatKernel
