-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Moser.WeakSolutionEnergyInterface
public import HeatKernel.Moser.WeakSolutionCutoffDualEquation
public import HeatKernel.Moser.WeakSolutionEnergyIdentityLimits
public import HeatKernel.Form.LocalEnergyAlgebra
public import HeatKernel.Moser.MeanValueNonnegativeCylinder
import Mathlib.Tactic

/-! # Nonnegative cutoff energy curves for measurable elliptic coefficients -/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set MeasureTheory TopologicalSpace RothschildStein
namespace HeatKernel

/-- A signed local weak solution with measurable elliptic coefficients supplies its
actual compatible cutoff energy curve. Measurable elliptic coefficients and
smooth compactly supported cutoffs provide the bounds needed by the time interface. -/
theorem IsLocalWeakSolution.exists_signed_smooth_cutoff_energy_pair {N q : ℕ}
    (G : HomogeneousGroup N) (hq : q ≤ N) (hqpos : 0 < q)
    (hw : ∀ i : Fin q, G.weight (Fin.castLE hq i) = 1)
    (hspan : bracketSpansOn univ (G.horizontalFields hq))
    (coeff : ℝ → (Fin N → ℝ) → Fin q → Fin q → ℝ)
    (I : Opens ℝ) (U V : Opens (Fin N → ℝ)) {u : ℝ → (Fin N → ℝ) → ℝ}
    (hu : IsLocalWeakSolution G hq hqpos hw hspan
      coeff I U u)
    (ha : ∀ i j, Measurable (fun z : ℝ × (Fin N → ℝ) => coeff z.1 z.2 i j))
    {lower upper : ℝ} (hlower : 0 ≤ lower)
    (hbound : ∀ᵐ z : ℝ × (Fin N → ℝ) ∂volume,
      (∀ i j, coeff z.1 z.2 i j = coeff z.1 z.2 j i) ∧ ∀ ξ : Fin q → ℝ,
        lower * ∑ i, ξ i ^ 2 ≤ ∑ i, ∑ j, coeff z.1 z.2 i j * ξ i * ξ j ∧
        ∑ i, ∑ j, coeff z.1 z.2 i j * ξ i * ξ j ≤ upper * ∑ i, ξ i ^ 2)
    {A B : ℝ} (hJ : Icc A B ⊆ (I : Set ℝ))
    {φ : (Fin N → ℝ) → ℝ} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hφunit : ∀ x, φ x ∈ Icc (0 : ℝ) 1)
    (hc : HasCompactSupport φ) (hU : tsupport φ ⊆ (U : Set (Fin N → ℝ)))
    (hV : tsupport φ ⊆ (V : Set (Fin N → ℝ))) :
    ∃ (g : Fin q → ℝ → (Fin N → ℝ) → ℝ)
      (v : ℝ → zeroBoundaryGraph V (G.horizontalFields hq))
      (F : ℝ → (zeroBoundaryGraph V (G.horizontalFields hq) →L[ℝ] ℝ)),
      WeakSolutionEnergyInterface (G.horizontalFields hq)
        coeff I U u g ∧
      IsZeroBoundaryWeakCutoffEnergyTimePair V (G.horizontalFields hq)
        coeff (Icc A B) u g φ
        (fun i => fieldDerivative (G.horizontalFields hq i) φ) v F := by
  classical
  have hX := G.horizontalFields_contDiff hq
  obtain ⟨g, hg⟩ := hu.exists_weak_solution_energy_interface G hq hqpos hw hspan
    coeff I U ha hlower hbound
  have hD (i : Fin q) : ContDiff ℝ (⊤ : ℕ∞)
      (fieldDerivative (G.horizontalFields hq i) φ) := by
    simpa only [Opens.coe_top, contDiffOn_univ] using
      S.contDiffOn_fieldDerivative ⊤ (G.horizontalFields hq i) φ (hX i).contDiffOn hφ.contDiffOn
  have hcD (i : Fin q) : HasCompactSupport (fieldDerivative (G.horizontalFields hq i) φ) :=
    hc.of_isClosed_subset (isClosed_tsupport _)
      (S.tsupport_fieldDerivative_subset (G.horizontalFields hq i) φ)
  choose C hC using fun i => (hcD i).exists_bound_of_continuous (hD i).continuous
  have hC0 (i : Fin q) : 0 ≤ C i := (norm_nonneg _).trans (hC i 0)
  have hCs : 0 ≤ ∑ i, C i := Finset.sum_nonneg fun i _ => hC0 i
  have hd (i : Fin q) : ∀ᵐ x ∂volume, ‖fieldDerivative (G.horizontalFields hq i) φ x‖ ≤ ∑ j, C j :=
    Filter.Eventually.of_forall fun x => (hC i x).trans
      (Finset.single_le_sum (fun j _ => hC0 j) (Finset.mem_univ i))
  obtain ⟨v, F, hp⟩ := hg.cutoff_time_curves (Icc A B) isCompact_Icc hJ V φ
    (fun i => fieldDerivative (G.horizontalFields hq i) φ)
    (memLocalEnergy_of_contDiff ⊤ _ hX hφ)
    (fun i => S.hasWeakWordDeriv_classical ⊤ _ (fun j => (hX j).contDiffOn) [i] φ hφ.contDiffOn)
    1 (∑ i, C i) (by norm_num) hCs
    (fun x => by simpa only [Real.norm_eq_abs, abs_of_nonneg (hφunit x).1] using (hφunit x).2)
    hd hc hU hV
  exact ⟨g, v, F, hg, hp⟩

/-- A nonnegative local weak solution with measurable elliptic coefficients supplies its
actual compatible cutoff energy curve. Measurable elliptic coefficients and
smooth compactly supported cutoffs provide the bounds needed by the time interface. -/
theorem IsLocalWeakSolution.exists_smooth_cutoff_energy_pair {N q : ℕ}
    (G : HomogeneousGroup N) (hq : q ≤ N) (hqpos : 0 < q)
    (hw : ∀ i : Fin q, G.weight (Fin.castLE hq i) = 1)
    (hspan : bracketSpansOn univ (G.horizontalFields hq))
    (coeff : ℝ → (Fin N → ℝ) → Fin q → Fin q → ℝ)
    (I : Opens ℝ) (U V : Opens (Fin N → ℝ)) {u : ℝ → (Fin N → ℝ) → ℝ}
    (hu : IsLocalWeakSolution G hq hqpos hw hspan
      coeff I U u)
    (ha : ∀ i j, Measurable (fun z : ℝ × (Fin N → ℝ) => coeff z.1 z.2 i j))
    {lower upper : ℝ} (hlower : 0 ≤ lower)
    (hbound : ∀ᵐ z : ℝ × (Fin N → ℝ) ∂volume,
      (∀ i j, coeff z.1 z.2 i j = coeff z.1 z.2 j i) ∧ ∀ ξ : Fin q → ℝ,
        lower * ∑ i, ξ i ^ 2 ≤ ∑ i, ∑ j, coeff z.1 z.2 i j * ξ i * ξ j ∧
        ∑ i, ∑ j, coeff z.1 z.2 i j * ξ i * ξ j ≤ upper * ∑ i, ξ i ^ 2)
    (hu0 : ∀ᵐ z : ℝ × (Fin N → ℝ)
      ∂volume.restrict ((I : Set ℝ) ×ˢ (U : Set (Fin N → ℝ))), 0 ≤ u z.1 z.2)
    {A B : ℝ} (hJ : Icc A B ⊆ (I : Set ℝ))
    {φ : (Fin N → ℝ) → ℝ} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hφunit : ∀ x, φ x ∈ Icc (0 : ℝ) 1)
    (hc : HasCompactSupport φ) (hU : tsupport φ ⊆ (U : Set (Fin N → ℝ)))
    (hV : tsupport φ ⊆ (V : Set (Fin N → ℝ))) :
    ∃ (g : Fin q → ℝ → (Fin N → ℝ) → ℝ)
      (v : ℝ → zeroBoundaryGraph V (G.horizontalFields hq))
      (F : ℝ → (zeroBoundaryGraph V (G.horizontalFields hq) →L[ℝ] ℝ)),
      WeakSolutionEnergyInterface (G.horizontalFields hq)
        coeff I U u g ∧
      IsZeroBoundaryWeakCutoffEnergyTimePair V (G.horizontalFields hq)
        coeff (Icc A B) u g φ
        (fun i => fieldDerivative (G.horizontalFields hq i) φ) v F ∧
      ∀ᵐ t ∂volume.restrict (Icc A B), ∀ᵐ x ∂volume,
        0 ≤ (v t : GradientSpace (N := N) ⊤ q).fst x := by
  obtain ⟨g, v, F, hg, hp⟩ := hu.exists_signed_smooth_cutoff_energy_pair
    G hq hqpos hw hspan coeff I U V ha hlower hbound hJ hφ hφunit hc hU hV
  refine ⟨g, v, F, hg, hp, ?_⟩
  have hn := (ae_ae_nonneg_of_nonneg_on_product I.isOpen.measurableSet
    U.isOpen.measurableSet hu0).filter_mono
      (ae_mono (Measure.restrict_le_self : volume.restrict (Icc A B) ≤ volume))
  filter_upwards [hp.2.2.1, self_mem_ae_restrict measurableSet_Icc, hn] with t ht htm hnt
  filter_upwards [ht, hnt] with x hx hnx
  rw [hx]
  by_cases hz : φ x = 0
  · simp only [hz, mul_zero, le_refl]
  · have hxU := hU (subset_tsupport φ (Function.mem_support.mpr hz))
    exact mul_nonneg (hnx (hJ htm) hxU) (hφunit x).1

end HeatKernel
