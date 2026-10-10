-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Form.ParabolicEnergyCurves
public import RothschildStein.S.WeakDeriv
import Mathlib.Tactic

/-! # Changes of representatives of local weak solutions

The local energy bounds and the spacetime test identity depend only on the
almost-everywhere class on the open cylinder. A nonnegative representative can
therefore be used whenever nonnegativity is known almost everywhere.
-/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set MeasureTheory Filter TopologicalSpace RothschildStein
open scoped ENNReal
namespace HeatKernel

/-- A change on a product null set preserves the local parabolic energy bounds,
with the same horizontal-gradient representative. -/
theorem HasLocalParabolicEnergyBounds.congr_value {N q : ℕ}
    {I : Opens ℝ} {U : Opens (Fin N → ℝ)}
    {u v : ℝ → (Fin N → ℝ) → ℝ} {g : Fin q → ℝ → (Fin N → ℝ) → ℝ}
    (hu : HasLocalParabolicEnergyBounds I U u g)
    (huv : (fun z : ℝ × (Fin N → ℝ) => u z.1 z.2) =ᵐ[
      volume.restrict ((I : Set ℝ) ×ˢ (U : Set (Fin N → ℝ)))]
        (fun z => v z.1 z.2)) :
    HasLocalParabolicEnergyBounds I U v g := by
  have hprod : (fun z : ℝ × (Fin N → ℝ) => u z.1 z.2) =ᵐ[
      (volume.restrict (I : Set ℝ)).prod (volume.restrict (U : Set (Fin N → ℝ)))]
        (fun z => v z.1 z.2) := by
    simpa only [Measure.prod_restrict, ← Measure.volume_eq_prod] using huv
  have htime := Measure.ae_ae_of_ae_prod hprod
  intro J K hJ hJI hK hKU
  obtain ⟨hbound, hgrad⟩ := hu J K hJ hJI hK hKU
  refine ⟨?_, hgrad⟩
  have hnorm : (fun t => eLpNorm (u t) 2 (volume.restrict K)) =ᵐ[volume.restrict J]
      (fun t => eLpNorm (v t) 2 (volume.restrict K)) := by
    filter_upwards [ae_restrict_of_ae_restrict_of_subset hJI htime] with t ht
    exact eLpNorm_congr_ae (ae_restrict_of_ae_restrict_of_subset hKU ht)
  exact (essSup_congr_ae hnorm) ▸ hbound

/-- Compact support makes the test identity invariant under changes on a null
set inside the cylinder, without any condition on the exterior values. -/
theorem SatisfiesParabolicTestIdentity.congr_value {N q : ℕ}
    {X : Fin q → (Fin N → ℝ) → (Fin N → ℝ)}
    {a : ℝ → (Fin N → ℝ) → Fin q → Fin q → ℝ}
    {I : Opens ℝ} {U : Opens (Fin N → ℝ)}
    {u v : ℝ → (Fin N → ℝ) → ℝ} {g : Fin q → ℝ → (Fin N → ℝ) → ℝ}
    (hu : SatisfiesParabolicTestIdentity X a I U u g)
    (huv : (fun z : ℝ × (Fin N → ℝ) => u z.1 z.2) =ᵐ[
      volume.restrict ((I : Set ℝ) ×ˢ (U : Set (Fin N → ℝ)))]
        (fun z => v z.1 z.2)) :
    SatisfiesParabolicTestIdentity X a I U v g := by
  intro φ hφ hc hs
  obtain ⟨hi, hid⟩ := hu φ hφ hc hs
  have hrep : (fun z : ℝ × (Fin N → ℝ) =>
      -(u z.1 z.2 * fderiv ℝ φ z (1, 0)) +
        ∑ i, ∑ j, a z.1 z.2 i j * g j z.1 z.2 * fderiv ℝ φ z (0, X i z.2)) =ᵐ[volume]
      (fun z => -(v z.1 z.2 * fderiv ℝ φ z (1, 0)) +
        ∑ i, ∑ j, a z.1 z.2 i j * g j z.1 z.2 * fderiv ℝ φ z (0, X i z.2)) := by
    filter_upwards [ae_imp_of_ae_restrict huv] with z hz
    by_cases hm : z ∈ (I : Set ℝ) ×ˢ (U : Set (Fin N → ℝ))
    · simp only [hz hm]
    · have hn : z ∉ tsupport φ := fun h => hm (hs h)
      simp only [fderiv_of_notMem_tsupport ℝ hn, zero_apply, mul_zero, neg_zero,
        Finset.sum_const_zero, add_zero]
  exact ⟨hi.congr hrep, (integral_congr_ae hrep).symm.trans hid⟩

/-- The literal local weak solution class depends only on the almost-everywhere
values on its open cylinder. -/
theorem IsLocalWeakSolution.congr_ae {N q : ℕ}
    {G : HomogeneousGroup N} {hq : q ≤ N} {hqpos : 0 < q}
    {hw : ∀ i : Fin q, G.weight (Fin.castLE hq i) = 1}
    {hspan : bracketSpansOn univ (G.horizontalFields hq)}
    {a : ℝ → (Fin N → ℝ) → Fin q → Fin q → ℝ}
    {I : Opens ℝ} {U : Opens (Fin N → ℝ)} {u v : ℝ → (Fin N → ℝ) → ℝ}
    (hu : IsLocalWeakSolution G hq hqpos hw hspan a I U u)
    (huv : (fun z : ℝ × (Fin N → ℝ) => u z.1 z.2) =ᵐ[
      volume.restrict ((I : Set ℝ) ×ˢ (U : Set (Fin N → ℝ)))]
        (fun z => v z.1 z.2)) :
    IsLocalWeakSolution G hq hqpos hw hspan a I U v := by
  obtain ⟨hm, g, hweak, henergy, htest⟩ := hu
  refine ⟨hm.congr huv, g, ?_, ?_, ?_⟩
  · have hprod : (fun z : ℝ × (Fin N → ℝ) => u z.1 z.2) =ᵐ[
        (volume.restrict (I : Set ℝ)).prod (volume.restrict (U : Set (Fin N → ℝ)))]
          (fun z => v z.1 z.2) := by
      simpa only [Measure.prod_restrict, ← Measure.volume_eq_prod] using huv
    filter_upwards [hweak, Measure.ae_ae_of_ae_prod hprod] with t ht hvalues
    exact fun i => S.hasWeakWordDeriv_congr_ae (G.horizontalFields hq) U
      (ht i) hvalues Filter.EventuallyEq.rfl
  · exact HasLocalParabolicEnergyBounds.congr_value henergy huv
  · exact SatisfiesParabolicTestIdentity.congr_value htest huv

/-- An almost-everywhere nonnegative local weak solution has the globally
nonnegative representative `max u 0`, with the same equation on the cylinder. -/
theorem IsLocalWeakSolution.max_zero_of_ae_nonneg {N q : ℕ}
    {G : HomogeneousGroup N} {hq : q ≤ N} {hqpos : 0 < q}
    {hw : ∀ i : Fin q, G.weight (Fin.castLE hq i) = 1}
    {hspan : bracketSpansOn univ (G.horizontalFields hq)}
    {a : ℝ → (Fin N → ℝ) → Fin q → Fin q → ℝ}
    {I : Opens ℝ} {U : Opens (Fin N → ℝ)} {u : ℝ → (Fin N → ℝ) → ℝ}
    (hu : IsLocalWeakSolution G hq hqpos hw hspan a I U u)
    (hn : ∀ᵐ z ∂volume.restrict ((I : Set ℝ) ×ˢ (U : Set (Fin N → ℝ))),
      0 ≤ u z.1 z.2) :
    IsLocalWeakSolution G hq hqpos hw hspan a I U (fun t x => max (u t x) 0) := by
  exact hu.congr_ae (hn.mono fun _ hz => (max_eq_left hz).symm)

end HeatKernel
