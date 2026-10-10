-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Bridge.CompactLocalGradient
public import HeatKernel.Sobolev.WeightedMeanExtended
public import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Tactic

/-! # Weighted quadratic moments of local horizontal energy functions -/

@[expose] public section
open Set MeasureTheory TopologicalSpace RothschildStein
namespace HeatKernel.Sobolev

/-- A bounded measurable weight with compact interior support gives integrable
quadratic value and weak-gradient moments of a local horizontal energy function. -/
theorem integrable_weighted_local_energy_moments {N q : ℕ}
    (U : Opens (Fin N → ℝ)) (X : Fin q → (Fin N → ℝ) → (Fin N → ℝ))
    (hX : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (X i))
    {f : (Fin N → ℝ) → ℝ} {g : Fin q → (Fin N → ℝ) → ℝ}
    (hf : MemLocalEnergy U X f) (hg : ∀ i, hasWeakWordDeriv X U [i] f (g i))
    {K : Set (Fin N → ℝ)} (hK : IsCompact K) (hKU : K ⊆ (U : Set (Fin N → ℝ)))
    {w : (Fin N → ℝ) → ℝ} (hw : Measurable w) {C : ℝ} (hb : ∀ x, ‖w x‖ ≤ C)
    (hs : Function.support w ⊆ K) :
    (∀ c : ℝ, Integrable (fun x => w x * (f x - c) ^ 2)) ∧
      Integrable (fun x => w x * ∑ i, (g i x) ^ 2) := by
  let : IsFiniteMeasure (volume.restrict K) := isFiniteMeasure_restrict.mpr hK.measure_ne_top
  have hfK := hf.memLp_restrict_compact U X hK hKU
  have hgK (i : Fin q) := hf.memLp_weak_gradient_restrict_compact U X hX i (hg i) hK hKU
  have hzero (x : Fin N → ℝ) (hx : x ∉ K) : w x = 0 := by
    by_contra hn
    exact hx (hs hn)
  refine ⟨?_, ?_⟩
  · intro c
    have hc : MemLp (fun _ : Fin N → ℝ => c) 2 (volume.restrict K) := memLp_const c
    have hi : IntegrableOn (fun x => (f x - c) ^ 2) K volume := by
      change Integrable (fun x => (f x - c) ^ 2) (volume.restrict K)
      exact (hfK.sub hc).integrable_sq
    exact integrable_mul_of_bounded_support_weight hK.measurableSet hw hb hzero hi
  · have hi : IntegrableOn (fun x => ∑ i, (g i x) ^ 2) K volume :=
      integrable_finsetSum Finset.univ (fun i _ => (hgK i).integrable_sq)
    exact integrable_mul_of_bounded_support_weight hK.measurableSet hw hb hzero hi

end HeatKernel.Sobolev
