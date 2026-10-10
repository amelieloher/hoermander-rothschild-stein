-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Geometry.WeakGradientLinearity
public import HeatKernel.Geometry.CarnotPoint

/-! The sharp joint weak horizontal gradient bound for horizontal Lipschitz functions. -/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set MeasureTheory RothschildStein Filter TopologicalSpace
open scoped NNReal ENNReal Topology BigOperators
namespace HeatKernel

/-- A continuous horizontal Lipschitz function has a weak horizontal gradient with joint
Euclidean norm at most its Lipschitz constant. -/
theorem exists_weak_horizontal_gradient {N q : ℕ} (G : HomogeneousGroup N) (hq : q ≤ N)
    (L : ℝ≥0) {f : (Fin N → ℝ) → ℝ} (hf : Continuous f)
    (hLip : ∀ x y, edist (f x) (f y) ≤ (L : ℝ≥0∞) * horizontalL2Distance (G.horizontalFields hq) x y) :
    ∃ g : Fin q → (Fin N → ℝ) → ℝ,
      (∀ i, hasWeakWordDeriv (G.horizontalFields hq) ⊤ [i] f (g i)) ∧
      ∀ᵐ x ∂MeasureTheory.volume, Real.sqrt (∑ i, g i x ^ 2) ≤ L := by
  classical
  choose g hg _hb using fun i : Fin q =>
    exists_bounded_weak_horizontal_derivative G hq (Pi.single i 1) L hf hLip
  have hgi : ∀ i, hasWeakWordDeriv (G.horizontalFields hq) ⊤ [i] f (g i) := by
    intro i
    have hi := hg i
    rw [horizontalTangent_single] at hi
    exact ⟨hi.1, hi.2.1, fun ψ => by
      simpa only [wordTranspose, HomogeneousGroup.horizontalFields, G2.canonicalField_eq_leftField] using hi.2.2 ψ⟩
  refine ⟨g, hgi, ?_⟩
  apply ae_sqrt_sum_sq_le_of_rat_directional_bounds g L.coe_nonneg
  intro b
  let c : Fin q → ℝ := fun i => (b i : ℝ)
  obtain ⟨D, hD, hb⟩ := exists_bounded_weak_horizontal_derivative G hq c L hf hLip
  have he := S.hasWeakWordDeriv_unique
    (fun _ : Fin 1 => G2.leftField G (horizontalTangent hq c)) ⊤
    (hasWeakWordDeriv_horizontal_linearCombination G hq c hf g hgi) hD
  have he' : (fun x => ∑ i, c i * g i x) =ᵐ[volume] D := by
    simpa only [Opens.coe_top, Measure.restrict_univ] using he
  filter_upwards [he', hb] with x hx hbx
  rw [← hx] at hbx
  exact hbx

/-- A Lipschitz function on the horizontal metric carrier has coordinate weak derivatives
with the sharp joint horizontal norm bound. -/
theorem CarnotPoint.exists_weak_horizontal_gradient {N q : ℕ} (G : HomogeneousGroup N)
    (hq : q ≤ N) (hqpos : 0 < q) (hspan : bracketSpansOn univ (G.horizontalFields hq))
    {L : ℝ≥0} {f : CarnotPoint G hq hqpos hspan → ℝ} (hf : LipschitzWith L f) :
    ∃ g : Fin q → (Fin N → ℝ) → ℝ,
      (∀ i, hasWeakWordDeriv (G.horizontalFields hq) ⊤ [i] f (g i)) ∧
      ∀ᵐ x ∂MeasureTheory.volume, Real.sqrt (∑ i, g i x ^ 2) ≤ L := by
  have hc : Continuous (f : (Fin N → ℝ) → ℝ) := hf.continuous
  apply HeatKernel.exists_weak_horizontal_gradient G hq L hc
  intro x y
  exact hf x y

end HeatKernel
