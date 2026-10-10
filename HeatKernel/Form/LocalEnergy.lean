-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Form.CompactMultipliers
public import Mathlib.Topology.Separation.Regular

/-! # Local representatives of the horizontal energy domain -/

@[expose] public section

noncomputable section

open Set MeasureTheory TopologicalSpace RothschildStein

namespace HeatKernel

variable {N q : ℕ} (U : Opens (Fin N → ℝ))
    (X : Fin q → (Fin N → ℝ) → (Fin N → ℝ))

/-- A measurable function belongs locally to the energy domain if each relatively compact
open subset has a global energy representative. -/
def MemLocalEnergy (f : (Fin N → ℝ) → ℝ) : Prop :=
  AEStronglyMeasurable f (volume.restrict (U : Set (Fin N → ℝ))) ∧
  ∀ V : Opens (Fin N → ℝ), IsCompact (closure (V : Set (Fin N → ℝ))) →
    closure (V : Set (Fin N → ℝ)) ⊆ (U : Set (Fin N → ℝ)) →
    ∃ w : energyGraph (N := N) ⊤ X,
      (w : GradientSpace (N := N) ⊤ q).fst =ᵐ[volume.restrict (V : Set (Fin N → ℝ))] f

/-- A compact set in an open set has an open neighborhood with compact closure inside it. -/
theorem exists_precompact_open_of_isCompact {K : Set (Fin N → ℝ)} (hc : IsCompact K)
    (hs : K ⊆ (U : Set (Fin N → ℝ))) :
    ∃ V : Opens (Fin N → ℝ), K ⊆ (V : Set (Fin N → ℝ)) ∧
      IsCompact (closure (V : Set (Fin N → ℝ))) ∧
      closure (V : Set (Fin N → ℝ)) ⊆ (U : Set (Fin N → ℝ)) := by
  obtain ⟨W, hWo, hKW, hWc⟩ := exists_isOpen_superset_and_isCompact_closure hc
  obtain ⟨V, hVo, hKV, hVU⟩ := hc.exists_isOpen_closure_subset
    ((U.isOpen.inter hWo).mem_nhdsSet.mpr (subset_inter hs hKW))
  exact ⟨⟨V, hVo⟩, hKV,
    hWc.of_isClosed_subset isClosed_closure (hVU.trans (inter_subset_right.trans subset_closure)),
    hVU.trans inter_subset_left⟩

/-- Local energy functions are square integrable on compact subsets. -/
theorem MemLocalEnergy.memLp_restrict_compact {f : (Fin N → ℝ) → ℝ}
    (hf : MemLocalEnergy U X f) {K : Set (Fin N → ℝ)}
    (hc : IsCompact K) (hs : K ⊆ (U : Set (Fin N → ℝ))) :
    MemLp f 2 (volume.restrict K) := by
  obtain ⟨V, hKV, hVc, hVU⟩ := exists_precompact_open_of_isCompact U hc hs
  obtain ⟨w, hw⟩ := hf.2 V hVc hVU
  have hp : MemLp ((w : GradientSpace (N := N) ⊤ q).fst : (Fin N → ℝ) → ℝ) 2 volume := by
    simpa only [Opens.coe_top, Measure.restrict_univ] using
      Lp.memLp (w : GradientSpace (N := N) ⊤ q).fst
  exact (hp.restrict K).ae_eq (ae_restrict_of_ae_restrict_of_subset hKV hw)

/-- A smooth compact cutoff of a local energy function has a global energy representative. -/
theorem MemLocalEnergy.exists_mul_smooth_compact {f φ : (Fin N → ℝ) → ℝ}
    (hf : MemLocalEnergy U X f) (hX : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (X i))
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hc : HasCompactSupport φ)
    (hs : tsupport φ ⊆ (U : Set (Fin N → ℝ))) :
    ∃ z : energyGraph (N := N) ⊤ X,
      (z : GradientSpace (N := N) ⊤ q).fst =ᵐ[volume] (fun x => f x * φ x) := by
  obtain ⟨V, hKV, hVc, hVU⟩ := exists_precompact_open_of_isCompact U hc hs
  obtain ⟨w, hw⟩ := hf.2 V hVc hVU
  obtain ⟨z, hzf, _⟩ := exists_energyGraph_mul_smooth_compact X hX w hφ hc
  refine ⟨z, hzf.trans ?_⟩
  filter_upwards [ae_imp_of_ae_restrict hw] with x hx
  by_cases hzero : φ x = 0
  · simp only [hzero, mul_zero]
  · rw [hx (hKV (subset_tsupport φ hzero))]

/-- A local cutoff product has the Leibniz gradient of any representative on a
relatively compact neighborhood of the cutoff support. -/
theorem MemLocalEnergy.exists_mul_smooth_compact_gradient {f φ : (Fin N → ℝ) → ℝ}
    (hf : MemLocalEnergy U X f) (hX : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (X i))
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hc : HasCompactSupport φ)
    (hs : tsupport φ ⊆ (U : Set (Fin N → ℝ))) :
    ∃ (V : Opens (Fin N → ℝ)) (w z : energyGraph (N := N) ⊤ X),
      tsupport φ ⊆ (V : Set (Fin N → ℝ)) ∧
      IsCompact (closure (V : Set (Fin N → ℝ))) ∧
      closure (V : Set (Fin N → ℝ)) ⊆ (U : Set (Fin N → ℝ)) ∧
      (w : GradientSpace (N := N) ⊤ q).fst =ᵐ[volume.restrict (V : Set (Fin N → ℝ))] f ∧
      (z : GradientSpace (N := N) ⊤ q).fst =ᵐ[volume] (fun x => f x * φ x) ∧
      ∀ i, (z : GradientSpace (N := N) ⊤ q).snd i =ᵐ[volume]
        (fun x => (w : GradientSpace (N := N) ⊤ q).snd i x * φ x +
          f x * fieldDerivative (X i) φ x) := by
  obtain ⟨V, hKV, hVc, hVU⟩ := exists_precompact_open_of_isCompact U hc hs
  obtain ⟨w, hw⟩ := hf.2 V hVc hVU
  obtain ⟨z, hzf, hzg⟩ := exists_energyGraph_mul_smooth_compact X hX w hφ hc
  refine ⟨V, w, z, hKV, hVc, hVU, hw, hzf.trans ?_, fun i => (hzg i).trans ?_⟩
  · filter_upwards [ae_imp_of_ae_restrict hw] with x hx
    by_cases hzero : φ x = 0
    · simp only [hzero, mul_zero]
    · rw [hx (hKV (subset_tsupport φ hzero))]
  · filter_upwards [ae_imp_of_ae_restrict hw] with x hx
    by_cases hmem : x ∈ tsupport φ
    · rw [hx (hKV hmem)]
    · have hz : fieldDerivative (X i) φ x = 0 := image_eq_zero_of_notMem_tsupport
        (fun ht => hmem (S.tsupport_fieldDerivative_subset (X i) φ ht))
      simp only [hz, mul_zero]

end HeatKernel
