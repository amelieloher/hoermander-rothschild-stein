-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Form.ParabolicEnergyCurves
public import RothschildStein.S.WeakDeriv

/-! # Addition of local weak parabolic solutions

The local energy bounds and the spacetime test identity are stable under addition.
-/

@[expose] public section

open Set MeasureTheory Filter TopologicalSpace RothschildStein
open scoped ENNReal BigOperators

namespace HeatKernel

/-- Addition preserves compact-cylinder energy bounds. -/
theorem HasLocalParabolicEnergyBounds.add {N q : ℕ}
    {I : Opens ℝ} {U : Opens (Fin N → ℝ)}
    {u v : ℝ → (Fin N → ℝ) → ℝ} {g h : Fin q → ℝ → (Fin N → ℝ) → ℝ}
    (hu : HasLocalParabolicEnergyBounds I U u g)
    (hv : HasLocalParabolicEnergyBounds I U v h) :
    HasLocalParabolicEnergyBounds I U (fun t x => u t x + v t x)
      (fun i t x => g i t x + h i t x) := by
  intro J K hJ hJI hK hKU
  obtain ⟨hub, hug⟩ := hu J K hJ hJI hK hKU
  obtain ⟨hvb, hvg⟩ := hv J K hJ hJI hK hKU
  refine ⟨?_, fun i => (hug i).add (hvg i)⟩
  apply lt_of_le_of_lt _ (ENNReal.add_lt_top.mpr ⟨hub, hvb⟩)
  refine essSup_le_of_ae_le _ ?_ (by isBoundedDefault)
  filter_upwards [ENNReal.ae_le_essSup (fun t => eLpNorm (u t) 2 (volume.restrict K)),
    ENNReal.ae_le_essSup (fun t => eLpNorm (v t) 2 (volume.restrict K))] with t ht hs
  exact (eLpNorm_add_le (by norm_num : (1 : ℝ≥0∞) ≤ 2)).trans (add_le_add ht hs)

/-- Addition preserves the spacetime test identity with the sum of the gradients. -/
theorem SatisfiesParabolicTestIdentity.add {N q : ℕ}
    {X : Fin q → (Fin N → ℝ) → (Fin N → ℝ)}
    {a : ℝ → (Fin N → ℝ) → Fin q → Fin q → ℝ}
    {I : Opens ℝ} {U : Opens (Fin N → ℝ)}
    {u v : ℝ → (Fin N → ℝ) → ℝ} {g h : Fin q → ℝ → (Fin N → ℝ) → ℝ}
    (hu : SatisfiesParabolicTestIdentity X a I U u g)
    (hv : SatisfiesParabolicTestIdentity X a I U v h) :
    SatisfiesParabolicTestIdentity X a I U (fun t x => u t x + v t x)
      (fun i t x => g i t x + h i t x) := by
  intro φ hφ hc hs
  obtain ⟨hui, hue⟩ := hu φ hφ hc hs
  obtain ⟨hvi, hve⟩ := hv φ hφ hc hs
  have he : (fun z : ℝ × (Fin N → ℝ) =>
      -((u z.1 z.2 + v z.1 z.2) * fderiv ℝ φ z (1, 0)) +
        ∑ i, ∑ j, a z.1 z.2 i j * (g j z.1 z.2 + h j z.1 z.2) *
          fderiv ℝ φ z (0, X i z.2)) =
      (fun z => -(u z.1 z.2 * fderiv ℝ φ z (1, 0)) +
        ∑ i, ∑ j, a z.1 z.2 i j * g j z.1 z.2 * fderiv ℝ φ z (0, X i z.2)) +
      (fun z => -(v z.1 z.2 * fderiv ℝ φ z (1, 0)) +
        ∑ i, ∑ j, a z.1 z.2 i j * h j z.1 z.2 * fderiv ℝ φ z (0, X i z.2)) := by
    funext z
    simp only [Pi.add_apply, mul_add, add_mul, Finset.sum_add_distrib]
    ring
  change Integrable (fun z : ℝ × (Fin N → ℝ) =>
      -((u z.1 z.2 + v z.1 z.2) * fderiv ℝ φ z (1, 0)) +
        ∑ i, ∑ j, a z.1 z.2 i j * (g j z.1 z.2 + h j z.1 z.2) *
          fderiv ℝ φ z (0, X i z.2)) ∧ _
  rw [he]
  exact ⟨hui.add hvi, (integral_add' hui hvi).trans (by rw [hue, hve, add_zero])⟩

/-- The sum of two local weak solutions with the same coefficients is a local weak solution. -/
theorem IsLocalWeakSolution.add {N q : ℕ}
    (G : HomogeneousGroup N) (hq : q ≤ N) (hqpos : 0 < q)
    (hw : ∀ i : Fin q, G.weight (Fin.castLE hq i) = 1)
    (hspan : bracketSpansOn univ (G.horizontalFields hq))
    {a : ℝ → (Fin N → ℝ) → Fin q → Fin q → ℝ}
    {I : Opens ℝ} {U : Opens (Fin N → ℝ)} {u v : ℝ → (Fin N → ℝ) → ℝ}
    (hu : IsLocalWeakSolution G hq hqpos hw hspan a I U u)
    (hv : IsLocalWeakSolution G hq hqpos hw hspan a I U v) :
    IsLocalWeakSolution G hq hqpos hw hspan a I U (fun t x => u t x + v t x) := by
  obtain ⟨hum, g, hgw, hge, hgt⟩ := hu
  obtain ⟨hvm, h, hhw, hhe, hht⟩ := hv
  refine ⟨hum.add hvm, fun i t x => g i t x + h i t x, ?_,
    HasLocalParabolicEnergyBounds.add hge hhe, SatisfiesParabolicTestIdentity.add hgt hht⟩
  filter_upwards [hgw, hhw] with t ht hs
  exact fun i => S.hasWeakWordDeriv_add (G.horizontalFields hq) U
    (fun j => (G.horizontalFields_contDiff hq j).contDiffOn) (ht i) (hs i)

end HeatKernel
